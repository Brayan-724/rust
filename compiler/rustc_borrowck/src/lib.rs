//! This query borrow-checks the MIR to (further) ensure it is not broken.

// tidy-alphabetical-start
#![allow(internal_features)]
#![doc(rust_logo)]
#![feature(assert_matches)]
#![feature(box_patterns)]
#![feature(file_buffered)]
#![feature(let_chains)]
#![feature(never_type)]
#![feature(rustc_attrs)]
#![feature(rustdoc_internals)]
#![feature(stmt_expr_attributes)]
#![feature(try_blocks)]
#![warn(unreachable_pub)]
// tidy-alphabetical-end

#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::marker::PhantomData;
use std::ops::Deref;

use consumers::{BodyWithBorrowckFacts, ConsumerOptions};
use rustc_data_structures::fx::{FxIndexMap, FxIndexSet};
use rustc_data_structures::graph::dominators::Dominators;
use rustc_errors::Diag;
use rustc_hir as hir;
use rustc_hir::def_id::LocalDefId;
use rustc_index::bit_set::{BitSet, ChunkedBitSet};
use rustc_index::{IndexSlice, IndexVec};
use rustc_infer::infer::{
    InferCtxt, NllRegionVariableOrigin, RegionVariableOrigin, TyCtxtInferExt,
};
use rustc_middle::mir::tcx::PlaceTy;
use rustc_middle::mir::*;
use rustc_middle::query::Providers;
use rustc_middle::ty::{self, ParamEnv, RegionVid, TyCtxt};
use rustc_middle::{bug, span_bug};
use rustc_mir_dataflow::Analysis;
use rustc_mir_dataflow::impls::{
    EverInitializedPlaces, MaybeInitializedPlaces, MaybeUninitializedPlaces,
};
use rustc_mir_dataflow::move_paths::{
    InitIndex, InitLocation, LookupResult, MoveData, MoveOutIndex, MovePathIndex,
};
use rustc_session::lint::builtin::UNUSED_MUT;
use rustc_span::{Span, Symbol};
use rustc_target::abi::FieldIdx;
use smallvec::SmallVec;
use tracing::{debug, instrument};

use self::diagnostics::{AccessKind, IllegalMoveOriginKind, MoveError, RegionName};
use self::location::LocationTable;
use self::path_utils::*;
use self::prefixes::PrefixSet;
use crate::session_diagnostics::VarNeedNotMut;

pub mod borrow_set;
mod borrowck_errors;
mod constraints;
mod dataflow;
mod def_use;
mod diagnostics;
mod facts;
mod location;
mod member_constraints;
mod nll;
mod path_utils;
mod place_ext;
mod places_conflict;
mod polonius;
mod prefixes;
mod region_infer;
mod renumber;
mod session_diagnostics;
mod type_check;
mod universal_regions;
mod used_muts;
mod util;

/// A public API provided for the Rust compiler consumers.
pub mod consumers;

use borrow_set::{BorrowData, BorrowSet};
use dataflow::{BorrowIndex, BorrowckDomain, BorrowckResults, Borrows};
use nll::PoloniusOutput;
use place_ext::PlaceExt;
use places_conflict::{PlaceConflictBias, places_conflict};
use region_infer::RegionInferenceContext;
use renumber::RegionCtxt;

rustc_fluent_macro::fluent_messages! { "../messages.ftl" }

/// Associate some local constants with the `'tcx` lifetime
struct TyCtxtConsts<'tcx>(PhantomData<&'tcx ()>);
impl<'tcx> TyCtxtConsts<'tcx> {
    const DEREF_PROJECTION: &'tcx [PlaceElem<'tcx>; 1] = &[ProjectionElem::Deref];
}

pub fn provide(providers: &mut Providers) {
    *providers = Providers { mir_borrowck, ..*providers };
}

#[allow(dead_code)]
fn mir_borrowck(tcx: TyCtxt<'_>, def: LocalDefId) -> &BorrowCheckResult<'_> {
    let (input_body, promoted) = tcx.mir_promoted(def);
    debug!("run query mir_borrowck: {}", tcx.def_path_str(def));

    let input_body: &Body<'_> = &input_body.borrow();

    if input_body.should_skip() || input_body.tainted_by_errors.is_some() {
        debug!("Skipping borrowck because of injected body or tainted body");
        // Let's make up a borrowck result! Fun times!
        let result = BorrowCheckResult {
            concrete_opaque_types: FxIndexMap::default(),
            closure_requirements: None,
            used_mut_upvars: SmallVec::new(),
            tainted_by_errors: input_body.tainted_by_errors,
        };
        return tcx.arena.alloc(result);
    }

    let promoted: &IndexSlice<_, _> = &promoted.borrow();
    let opt_closure_req = do_mir_borrowck(tcx, input_body, promoted, None).0;
    debug!("mir_borrowck done");

    tcx.arena.alloc(opt_closure_req)
}

/// Perform the actual borrow checking.
///
/// Use `consumer_options: None` for the default behavior of returning
/// [`BorrowCheckResult`] only. Otherwise, return [`BodyWithBorrowckFacts`] according
/// to the given [`ConsumerOptions`].
#[instrument(skip(tcx, input_body, input_promoted), fields(id=?input_body.source.def_id()), level = "debug")]
fn do_mir_borrowck<'tcx>(
    tcx: TyCtxt<'tcx>,
    input_body: &Body<'tcx>,
    input_promoted: &IndexSlice<Promoted, Body<'tcx>>,
    consumer_options: Option<ConsumerOptions>,
) -> (BorrowCheckResult<'tcx>, Option<Box<BodyWithBorrowckFacts<'tcx>>>) {
    let def = input_body.source.def_id().expect_local();
    let infcx = BorrowckInferCtxt::new(tcx, def);
    let param_env = tcx.param_env(def);

    let mut local_names = IndexVec::from_elem(None, &input_body.local_decls);
    for var_debug_info in &input_body.var_debug_info {
        if let VarDebugInfoContents::Place(place) = var_debug_info.value {
            if let Some(local) = place.as_local() {
                if let Some(prev_name) = local_names[local]
                    && var_debug_info.name != prev_name
                {
                    span_bug!(
                        var_debug_info.source_info.span,
                        "local {:?} has many names (`{}` vs `{}`)",
                        local,
                        prev_name,
                        var_debug_info.name
                    );
                }
                local_names[local] = Some(var_debug_info.name);
            }
        }
    }

    let mut diags = diags::BorrowckDiags::new();

    // Gather the upvars of a closure, if any.
    if let Some(e) = input_body.tainted_by_errors {
        infcx.set_tainted_by_errors(e);
    }

    // Replace all regions with fresh inference variables. This
    // requires first making our own copy of the MIR. This copy will
    // be modified (in place) to contain non-lexical lifetimes. It
    // will have a lifetime tied to the inference context.
    let mut body_owned = input_body.clone();
    let mut promoted = input_promoted.to_owned();
    let free_regions =
        nll::replace_regions_in_mir(&infcx, param_env, &mut body_owned, &mut promoted);
    let body = &body_owned; // no further changes

    // FIXME(-Znext-solver): A bit dubious that we're only registering
    // predefined opaques in the typeck root.
    if infcx.next_trait_solver() && !infcx.tcx.is_typeck_child(body.source.def_id()) {
        infcx.register_predefined_opaques_for_next_solver(def);
    }

    let location_table = LocationTable::new(body);

    let move_data = MoveData::gather_moves(body, tcx, param_env, |_| true);
    let promoted_move_data = promoted
        .iter_enumerated()
        .map(|(idx, body)| (idx, MoveData::gather_moves(body, tcx, param_env, |_| true)));

    let mut flow_inits = MaybeInitializedPlaces::new(tcx, body, &move_data)
        .into_engine(tcx, body)
        .pass_name("borrowck")
        .iterate_to_fixpoint()
        .into_results_cursor(body);

    let locals_are_invalidated_at_exit = tcx.hir().body_owner_kind(def).is_fn_or_closure();
    let borrow_set = BorrowSet::build(tcx, body, locals_are_invalidated_at_exit, &move_data);

    // Compute non-lexical lifetimes.
    let nll::NllOutput {
        regioncx,
        opaque_type_values,
        polonius_input,
        polonius_output,
        opt_closure_req,
        nll_errors,
    } = nll::compute_regions(
        &infcx,
        free_regions,
        body,
        &promoted,
        &location_table,
        param_env,
        &mut flow_inits,
        &move_data,
        &borrow_set,
        tcx.closure_captures(def),
        consumer_options,
    );

    // Dump MIR results into a file, if that is enabled. This let us
    // write unit-tests, as well as helping with debugging.
    // nll::dump_nll_mir(&infcx, body, &regioncx, &opt_closure_req, &borrow_set);

    // We also have a `#[rustc_regions]` annotation that causes us to dump
    // information.
    // nll::dump_annotation(
    //     &infcx,
    //     body,
    //     &regioncx,
    //     &opt_closure_req,
    //     &opaque_type_values,
    //     &mut diags,
    // );

    // The various `flow_*` structures can be large. We drop `flow_inits` here
    // so it doesn't overlap with the others below. This reduces peak memory
    // usage significantly on some benchmarks.
    drop(flow_inits);

    let flow_borrows = Borrows::new(tcx, body, &regioncx, &borrow_set)
        .into_engine(tcx, body)
        .pass_name("borrowck")
        .iterate_to_fixpoint();
    let flow_uninits = MaybeUninitializedPlaces::new(tcx, body, &move_data)
        .into_engine(tcx, body)
        .pass_name("borrowck")
        .iterate_to_fixpoint();
    let flow_ever_inits = EverInitializedPlaces::new(body, &move_data)
        .into_engine(tcx, body)
        .pass_name("borrowck")
        .iterate_to_fixpoint();

    let movable_coroutine =
        // The first argument is the coroutine type passed by value
        if let Some(local) = body.local_decls.raw.get(1)
        // Get the interior types and args which typeck computed
        && let ty::Coroutine(def_id, _) = *local.ty.kind()
        && tcx.coroutine_movability(def_id) == hir::Movability::Movable
    {
        true
    } else {
        false
    };

    for (idx, move_data) in promoted_move_data {
        use rustc_middle::mir::visit::Visitor;

        let promoted_body = &promoted[idx];
        let mut promoted_mbcx = MirBorrowckCtxt {
            infcx: &infcx,
            param_env,
            body: promoted_body,
            move_data: &move_data,
            location_table: &location_table, // no need to create a real one for the promoted, it is not used
            movable_coroutine,
            fn_self_span_reported: Default::default(),
            locals_are_invalidated_at_exit,
            access_place_error_reported: Default::default(),
            reservation_error_reported: Default::default(),
            uninitialized_error_reported: Default::default(),
            regioncx: &regioncx,
            used_mut: Default::default(),
            used_mut_upvars: SmallVec::new(),
            borrow_set: &borrow_set,
            upvars: &[],
            local_names: IndexVec::from_elem(None, &promoted_body.local_decls),
            region_names: RefCell::default(),
            next_region_name: RefCell::new(1),
            polonius_output: None,
            move_errors: Vec::new(),
            diags,
        };
        // MoveVisitor { ctxt: &mut promoted_mbcx }.visit_body(promoted_body);
        promoted_mbcx.report_move_errors();
        diags = promoted_mbcx.diags;
    }

    let mut mbcx = MirBorrowckCtxt {
        infcx: &infcx,
        param_env,
        body,
        move_data: &move_data,
        location_table: &location_table,
        movable_coroutine,
        locals_are_invalidated_at_exit,
        fn_self_span_reported: Default::default(),
        access_place_error_reported: Default::default(),
        reservation_error_reported: Default::default(),
        uninitialized_error_reported: Default::default(),
        regioncx: &regioncx,
        used_mut: Default::default(),
        used_mut_upvars: SmallVec::new(),
        borrow_set: &borrow_set,
        upvars: tcx.closure_captures(def),
        local_names,
        region_names: RefCell::default(),
        next_region_name: RefCell::new(1),
        polonius_output,
        move_errors: Vec::new(),
        diags,
    };

    // Compute and report region errors, if any.
    mbcx.report_region_errors(nll_errors);

    let mut results = BorrowckResults {
        ever_inits: flow_ever_inits,
        uninits: flow_uninits,
        borrows: flow_borrows,
    };

    rustc_mir_dataflow::visit_results(
        body,
        traversal::reverse_postorder(body).map(|(bb, _)| bb),
        &mut results,
        &mut mbcx,
    );

    mbcx.report_move_errors();

    // For each non-user used mutable variable, check if it's been assigned from
    // a user-declared local. If so, then put that local into the used_mut set.
    // Note that this set is expected to be small - only upvars from closures
    // would have a chance of erroneously adding non-user-defined mutable vars
    // to the set.
    let temporary_used_locals: FxIndexSet<Local> = mbcx
        .used_mut
        .iter()
        .filter(|&local| !mbcx.body.local_decls[*local].is_user_variable())
        .cloned()
        .collect();
    // For the remaining unused locals that are marked as mutable, we avoid linting any that
    // were never initialized. These locals may have been removed as unreachable code; or will be
    // linted as unused variables.
    let unused_mut_locals =
        mbcx.body.mut_vars_iter().filter(|local| !mbcx.used_mut.contains(local)).collect();
    mbcx.gather_used_muts(temporary_used_locals, unused_mut_locals);

    debug!("mbcx.used_mut: {:?}", mbcx.used_mut);

    let tainted_by_errors = mbcx.emit_errors();

    let result = BorrowCheckResult {
        concrete_opaque_types: opaque_type_values,
        closure_requirements: opt_closure_req,
        used_mut_upvars: mbcx.used_mut_upvars,
        tainted_by_errors,
    };

    let body_with_facts = if consumer_options.is_some() {
        let output_facts = mbcx.polonius_output;
        Some(Box::new(BodyWithBorrowckFacts {
            body: body_owned,
            promoted,
            borrow_set,
            region_inference_context: regioncx,
            location_table: polonius_input.as_ref().map(|_| location_table),
            input_facts: polonius_input,
            output_facts,
        }))
    } else {
        None
    };

    debug!("do_mir_borrowck: result = {:#?}", result);

    // println!("DEBUG: {result:#?}");

    (result, body_with_facts)
}

pub struct BorrowckInferCtxt<'tcx> {
    pub(crate) infcx: InferCtxt<'tcx>,
    pub(crate) reg_var_to_origin: RefCell<FxIndexMap<ty::RegionVid, RegionCtxt>>,
}

impl<'tcx> BorrowckInferCtxt<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> Self {
        let infcx = tcx.infer_ctxt().with_opaque_type_inference(def_id).build();
        BorrowckInferCtxt { infcx, reg_var_to_origin: RefCell::new(Default::default()) }
    }

    pub(crate) fn next_region_var<F>(
        &self,
        origin: RegionVariableOrigin,
        get_ctxt_fn: F,
    ) -> ty::Region<'tcx>
    where
        F: Fn() -> RegionCtxt,
    {
        let next_region = self.infcx.next_region_var(origin);
        let vid = next_region.as_var();

        if cfg!(debug_assertions) {
            debug!("inserting vid {:?} with origin {:?} into var_to_origin", vid, origin);
            let ctxt = get_ctxt_fn();
            let mut var_to_origin = self.reg_var_to_origin.borrow_mut();
            assert_eq!(var_to_origin.insert(vid, ctxt), None);
        }

        next_region
    }

    #[instrument(skip(self, get_ctxt_fn), level = "debug")]
    pub(crate) fn next_nll_region_var<F>(
        &self,
        origin: NllRegionVariableOrigin,
        get_ctxt_fn: F,
    ) -> ty::Region<'tcx>
    where
        F: Fn() -> RegionCtxt,
    {
        let next_region = self.infcx.next_nll_region_var(origin);
        let vid = next_region.as_var();

        if cfg!(debug_assertions) {
            debug!("inserting vid {:?} with origin {:?} into var_to_origin", vid, origin);
            let ctxt = get_ctxt_fn();
            let mut var_to_origin = self.reg_var_to_origin.borrow_mut();
            assert_eq!(var_to_origin.insert(vid, ctxt), None);
        }

        next_region
    }

    /// With the new solver we prepopulate the opaque type storage during
    /// MIR borrowck with the hidden types from HIR typeck. This is necessary
    /// to avoid ambiguities as earlier goals can rely on the hidden type
    /// of an opaque which is only constrained by a later goal.
    fn register_predefined_opaques_for_next_solver(&self, def_id: LocalDefId) {
        let tcx = self.tcx;
        // OK to use the identity arguments for each opaque type key, since
        // we remap opaques from HIR typeck back to their definition params.
        for data in tcx.typeck(def_id).concrete_opaque_types.iter().map(|(k, v)| (*k, *v)) {
            // HIR typeck did not infer the regions of the opaque, so we instantiate
            // them with fresh inference variables.
            let (key, hidden_ty) = tcx.fold_regions(data, |_, _| {
                self.next_nll_region_var_in_universe(
                    NllRegionVariableOrigin::Existential { from_forall: false },
                    ty::UniverseIndex::ROOT,
                )
            });

            self.inject_new_hidden_type_unchecked(key, hidden_ty);
        }
    }
}

impl<'tcx> Deref for BorrowckInferCtxt<'tcx> {
    type Target = InferCtxt<'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.infcx
    }
}

struct MirBorrowckCtxt<'a, 'infcx, 'tcx> {
    infcx: &'infcx BorrowckInferCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    body: &'a Body<'tcx>,
    move_data: &'a MoveData<'tcx>,

    /// Map from MIR `Location` to `LocationIndex`; created
    /// when MIR borrowck begins.
    location_table: &'a LocationTable,

    movable_coroutine: bool,
    /// This keeps track of whether local variables are free-ed when the function
    /// exits even without a `StorageDead`, which appears to be the case for
    /// constants.
    ///
    /// I'm not sure this is the right approach - @eddyb could you try and
    /// figure this out?
    locals_are_invalidated_at_exit: bool,
    /// This field keeps track of when borrow errors are reported in the access_place function
    /// so that there is no duplicate reporting. This field cannot also be used for the conflicting
    /// borrow errors that is handled by the `reservation_error_reported` field as the inclusion
    /// of the `Span` type (while required to mute some errors) stops the muting of the reservation
    /// errors.
    access_place_error_reported: FxIndexSet<(Place<'tcx>, Span)>,
    /// This field keeps track of when borrow conflict errors are reported
    /// for reservations, so that we don't report seemingly duplicate
    /// errors for corresponding activations.
    //
    // FIXME: ideally this would be a set of `BorrowIndex`, not `Place`s,
    // but it is currently inconvenient to track down the `BorrowIndex`
    // at the time we detect and report a reservation error.
    reservation_error_reported: FxIndexSet<Place<'tcx>>,
    /// This fields keeps track of the `Span`s that we have
    /// used to report extra information for `FnSelfUse`, to avoid
    /// unnecessarily verbose errors.
    fn_self_span_reported: FxIndexSet<Span>,
    /// This field keeps track of errors reported in the checking of uninitialized variables,
    /// so that we don't report seemingly duplicate errors.
    uninitialized_error_reported: FxIndexSet<Local>,
    /// This field keeps track of all the local variables that are declared mut and are mutated.
    /// Used for the warning issued by an unused mutable local variable.
    used_mut: FxIndexSet<Local>,
    /// If the function we're checking is a closure, then we'll need to report back the list of
    /// mutable upvars that have been used. This field keeps track of them.
    used_mut_upvars: SmallVec<[FieldIdx; 8]>,
    /// Region inference context. This contains the results from region inference and lets us e.g.
    /// find out which CFG points are contained in each borrow region.
    regioncx: &'a RegionInferenceContext<'tcx>,

    /// The set of borrows extracted from the MIR
    borrow_set: &'a BorrowSet<'tcx>,

    /// Information about upvars not necessarily preserved in types or MIR
    upvars: &'tcx [&'tcx ty::CapturedPlace<'tcx>],

    /// Names of local (user) variables (extracted from `var_debug_info`).
    local_names: IndexVec<Local, Option<Symbol>>,

    /// Record the region names generated for each region in the given
    /// MIR def so that we can reuse them later in help/error messages.
    region_names: RefCell<FxIndexMap<RegionVid, RegionName>>,

    /// The counter for generating new region names.
    next_region_name: RefCell<usize>,

    /// Results of Polonius analysis.
    polonius_output: Option<Box<PoloniusOutput>>,

    diags: diags::BorrowckDiags<'infcx, 'tcx>,
    move_errors: Vec<MoveError<'tcx>>,
}

// Check that:
// 1. assignments are always made to mutable locations (FIXME: does that still really go here?)
// 2. loans made in overlapping scopes do not conflict
// 3. assignments do not affect things loaned out as immutable
// 4. moves do not affect things loaned out in any way
impl<'a, 'tcx, R> rustc_mir_dataflow::ResultsVisitor<'a, 'tcx, R>
    for MirBorrowckCtxt<'a, '_, 'tcx>
{
    type Domain = BorrowckDomain<'a, 'tcx>;

    fn visit_statement_before_primary_effect(
        &mut self,
        _results: &mut R,
        state: &BorrowckDomain<'a, 'tcx>,
        stmt: &'a Statement<'tcx>,
        location: Location,
    ) {
        let span = stmt.source_info.span;

        match &stmt.kind {
            StatementKind::Assign(box (lhs, rhs)) => {
                // self.consume_rvalue(location, (rhs, span), state);
            }
            _ => {
                // NOP
            }
        }
    }
}

use self::AccessDepth::{Deep, Shallow};
use self::ReadOrWrite::{Activation, Read, Reservation, Write};

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum ArtificialField {
    ArrayLength,
    FakeBorrow,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum AccessDepth {
    /// From the RFC: "A *shallow* access means that the immediate
    /// fields reached at P are accessed, but references or pointers
    /// found within are not dereferenced. Right now, the only access
    /// that is shallow is an assignment like `x = ...;`, which would
    /// be a *shallow write* of `x`."
    Shallow(Option<ArtificialField>),

    /// From the RFC: "A *deep* access means that all data reachable
    /// through the given place may be invalidated or accesses by
    /// this action."
    Deep,

    /// Access is Deep only when there is a Drop implementation that
    /// can reach the data behind the reference.
    Drop,
}

/// Kind of access to a value: read or write
/// (For informational purposes only)
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum ReadOrWrite {
    /// From the RFC: "A *read* means that the existing data may be
    /// read, but will not be changed."
    Read(ReadKind),

    /// From the RFC: "A *write* means that the data may be mutated to
    /// new values or otherwise invalidated (for example, it could be
    /// de-initialized, as in a move operation).
    Write(WriteKind),

    /// For two-phase borrows, we distinguish a reservation (which is treated
    /// like a Read) from an activation (which is treated like a write), and
    /// each of those is furthermore distinguished from Reads/Writes above.
    Reservation(WriteKind),
    Activation(WriteKind, BorrowIndex),
}

/// Kind of read access to a value
/// (For informational purposes only)
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum ReadKind {
    Borrow(BorrowKind),
    Copy,
}

/// Kind of write access to a value
/// (For informational purposes only)
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum WriteKind {
    StorageDeadOrDrop,
    Replace,
    MutableBorrow(BorrowKind),
    Mutate,
    Move,
}

/// When checking permissions for a place access, this flag is used to indicate that an immutable
/// local place can be mutated.
//
// FIXME: @nikomatsakis suggested that this flag could be removed with the following modifications:
// - Split `is_mutable()` into `is_assignable()` (can be directly assigned) and
//   `is_declared_mutable()`.
// - Take flow state into consideration in `is_assignable()` for local variables.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum LocalMutationIsAllowed {
    Yes,
    /// We want use of immutable upvars to cause a "write to immutable upvar"
    /// error, not an "reassignment" error.
    ExceptUpvars,
    No,
}

#[derive(Copy, Clone, Debug)]
enum InitializationRequiringAction {
    Borrow,
    MatchOn,
    Use,
    Assignment,
    PartialAssignment,
}

#[derive(Debug)]
struct RootPlace<'tcx> {
    place_local: Local,
    place_projection: &'tcx [PlaceElem<'tcx>],
    is_local_mutation_allowed: LocalMutationIsAllowed,
}

impl InitializationRequiringAction {
    fn as_noun(self) -> &'static str {
        match self {
            InitializationRequiringAction::Borrow => "borrow",
            InitializationRequiringAction::MatchOn => "use", // no good noun
            InitializationRequiringAction::Use => "use",
            InitializationRequiringAction::Assignment => "assign",
            InitializationRequiringAction::PartialAssignment => "assign to part",
        }
    }

    fn as_verb_in_past_tense(self) -> &'static str {
        match self {
            InitializationRequiringAction::Borrow => "borrowed",
            InitializationRequiringAction::MatchOn => "matched on",
            InitializationRequiringAction::Use => "used",
            InitializationRequiringAction::Assignment => "assigned",
            InitializationRequiringAction::PartialAssignment => "partially assigned",
        }
    }

    fn as_general_verb_in_past_tense(self) -> &'static str {
        match self {
            InitializationRequiringAction::Borrow
            | InitializationRequiringAction::MatchOn
            | InitializationRequiringAction::Use => "used",
            InitializationRequiringAction::Assignment => "assigned",
            InitializationRequiringAction::PartialAssignment => "partially assigned",
        }
    }
}

impl<'a, 'tcx> MirBorrowckCtxt<'a, '_, 'tcx> {
    fn body(&self) -> &'a Body<'tcx> {
        self.body
    }

    #[allow(unreachable_code)]
    fn check_access_for_conflict(
        &mut self,
        location: Location,
        place_span: (Place<'tcx>, Span),
        sd: AccessDepth,
        rw: ReadOrWrite,
        state: &BorrowckDomain<'a, 'tcx>,
    ) -> bool {
        return false;

        let mut error_reported = false;

        // Use polonius output if it has been enabled.
        let mut polonius_output;
        let borrows_in_scope = if let Some(polonius) = &self.polonius_output {
            let location = self.location_table.start_index(location);
            polonius_output = BitSet::new_empty(self.borrow_set.len());
            for &idx in polonius.errors_at(location) {
                polonius_output.insert(idx);
            }
            &polonius_output
        } else {
            &state.borrows
        };

        each_borrow_involving_path(
            self,
            self.infcx.tcx,
            self.body,
            (sd, place_span.0),
            self.borrow_set,
            |borrow_index| borrows_in_scope.contains(borrow_index),
            |this, borrow_index, borrow| match (rw, borrow.kind) {
                // Obviously an activation is compatible with its own
                // reservation (or even prior activating uses of same
                // borrow); so don't check if they interfere.
                //
                // NOTE: *reservations* do conflict with themselves;
                // thus aren't injecting unsoundness w/ this check.)
                (Activation(_, activating), _) if activating == borrow_index => {
                    debug!(
                        "check_access_for_conflict place_span: {:?} sd: {:?} rw: {:?} \
                         skipping {:?} b/c activation of same borrow_index",
                        place_span,
                        sd,
                        rw,
                        (borrow_index, borrow),
                    );
                    Control::Continue
                }

                (Read(_), BorrowKind::Shared | BorrowKind::Fake(_))
                | (
                    Read(ReadKind::Borrow(BorrowKind::Fake(FakeBorrowKind::Shallow))),
                    BorrowKind::Mut { .. },
                ) => Control::Continue,

                (Reservation(_), BorrowKind::Fake(_) | BorrowKind::Shared) => {
                    // This used to be a future compatibility warning (to be
                    // disallowed on NLL). See rust-lang/rust#56254
                    Control::Continue
                }

                (Write(WriteKind::Move), BorrowKind::Fake(FakeBorrowKind::Shallow)) => {
                    // Handled by initialization checks.
                    Control::Continue
                }

                (Read(kind), BorrowKind::Mut { .. }) => {
                    // Reading from mere reservations of mutable-borrows is OK.
                    if !is_active(this.dominators(), borrow, location) {
                        assert!(allow_two_phase_borrow(borrow.kind));
                        return Control::Continue;
                    }

                    error_reported = true;
                    Control::Break
                }

                (Reservation(kind) | Activation(kind, _) | Write(kind), _) => {
                    match rw {
                        Reservation(..) => {
                            debug!(
                                "recording invalid reservation of \
                                 place: {:?}",
                                place_span.0
                            );
                            this.reservation_error_reported.insert(place_span.0);
                        }
                        Activation(_, activating) => {
                            debug!(
                                "observing check_place for activation of \
                                 borrow_index: {:?}",
                                activating
                            );
                        }
                        Read(..) | Write(..) => {}
                    }

                    error_reported = true;
                    Control::Break
                }
            },
        );

        error_reported
    }

    fn consume_rvalue(
        &mut self,
        location: Location,
        (rvalue, span): (&'a Rvalue<'tcx>, Span),
        state: &BorrowckDomain<'a, 'tcx>,
    ) {
        match rvalue {
            Rvalue::Aggregate(aggregate_kind, operands) => {
                // We need to report back the list of mutable upvars that were
                // moved into the closure and subsequently used by the closure,
                // in order to populate our used_mut set.
                match **aggregate_kind {
                    AggregateKind::Closure(def_id, _)
                    | AggregateKind::CoroutineClosure(def_id, _)
                    | AggregateKind::Coroutine(def_id, _) => {
                        let def_id = def_id.expect_local();
                        let BorrowCheckResult { used_mut_upvars, .. } =
                            self.infcx.tcx.mir_borrowck(def_id);
                        debug!("{:?} used_mut_upvars={:?}", def_id, used_mut_upvars);
                        for field in used_mut_upvars {
                            self.propagate_closure_used_mut_upvar(&operands[*field]);
                        }
                    }
                    AggregateKind::Adt(..)
                    | AggregateKind::Array(..)
                    | AggregateKind::Tuple { .. }
                    | AggregateKind::RawPtr(..) => (),
                }
            }

            _ => {}
        }
    }

    fn propagate_closure_used_mut_upvar(&mut self, operand: &Operand<'tcx>) {
        let propagate_closure_used_mut_place = |this: &mut Self, place: Place<'tcx>| {
            // We have three possibilities here:
            // a. We are modifying something through a mut-ref
            // b. We are modifying something that is local to our parent
            // c. Current body is a nested closure, and we are modifying path starting from
            //    a Place captured by our parent closure.

            // Handle (c), the path being modified is exactly the path captured by our parent
            if let Some(field) = this.is_upvar_field_projection(place.as_ref()) {
                this.used_mut_upvars.push(field);
                return;
            }

            for (place_ref, proj) in place.iter_projections().rev() {
                // Handle (a)
                if proj == ProjectionElem::Deref {
                    match place_ref.ty(this.body(), this.infcx.tcx).ty.kind() {
                        // We aren't modifying a variable directly
                        ty::Ref(_, _, hir::Mutability::Mut) => return,

                        _ => {}
                    }
                }

                // Handle (c)
                if let Some(field) = this.is_upvar_field_projection(place_ref) {
                    this.used_mut_upvars.push(field);
                    return;
                }
            }

            // Handle(b)
            this.used_mut.insert(place.local);
        };

        // This relies on the current way that by-value
        // captures of a closure are copied/moved directly
        // when generating MIR.
        match *operand {
            Operand::Move(place) | Operand::Copy(place) => {
                match place.as_local() {
                    Some(local) if !self.body.local_decls[local].is_user_variable() => {
                        if self.body.local_decls[local].ty.is_mutable_ptr() {
                            // The variable will be marked as mutable by the borrow.
                            return;
                        }
                        // This is an edge case where we have a `move` closure
                        // inside a non-move closure, and the inner closure
                        // contains a mutation:
                        //
                        // let mut i = 0;
                        // || { move || { i += 1; }; };
                        //
                        // In this case our usual strategy of assuming that the
                        // variable will be captured by mutable reference is
                        // wrong, since `i` can be copied into the inner
                        // closure from a shared reference.
                        //
                        // As such we have to search for the local that this
                        // capture comes from and mark it as being used as mut.

                        let Some(temp_mpi) = self.move_data.rev_lookup.find_local(local) else {
                            bug!("temporary should be tracked");
                        };
                        let init = if let [init_index] = *self.move_data.init_path_map[temp_mpi] {
                            &self.move_data.inits[init_index]
                        } else {
                            bug!("temporary should be initialized exactly once")
                        };

                        let InitLocation::Statement(loc) = init.location else {
                            bug!("temporary initialized in arguments")
                        };

                        let body = self.body;
                        let bbd = &body[loc.block];
                        let stmt = &bbd.statements[loc.statement_index];
                        debug!("temporary assigned in: stmt={:?}", stmt);

                        if let StatementKind::Assign(box (_, Rvalue::Ref(_, _, source))) = stmt.kind
                        {
                            propagate_closure_used_mut_place(self, source);
                        } else {
                            bug!(
                                "closures should only capture user variables \
                                 or references to user variables"
                            );
                        }
                    }
                    _ => propagate_closure_used_mut_place(self, place),
                }
            }
            Operand::Constant(..) => {}
        }
    }

    /// Reports an error if this is a borrow of local data.
    /// This is called for all Yield expressions on movable coroutines
    fn check_for_local_borrow(&mut self, borrow: &BorrowData<'tcx>, yield_span: Span) {
        debug!("check_for_local_borrow({:?})", borrow);

        if borrow_of_local_data(borrow.borrowed_place) {
            let err = self.cannot_borrow_across_coroutine_yield(
                self.retrieve_borrow_spans(borrow).var_or_use(),
                yield_span,
            );

            self.buffer_error(err);
        }
    }
    /// Currently MoveData does not store entries for all places in
    /// the input MIR. For example it will currently filter out
    /// places that are Copy; thus we do not track places of shared
    /// reference type. This routine will walk up a place along its
    /// prefixes, searching for a foundational place that *is*
    /// tracked in the MoveData.
    ///
    /// An Err result includes a tag indicated why the search failed.
    /// Currently this can only occur if the place is built off of a
    /// static variable, as we do not track those in the MoveData.
    fn move_path_closest_to(&mut self, place: PlaceRef<'tcx>) -> (PlaceRef<'tcx>, MovePathIndex) {
        match self.move_data.rev_lookup.find(place) {
            LookupResult::Parent(Some(mpi)) | LookupResult::Exact(mpi) => {
                (self.move_data.move_paths[mpi].place.as_ref(), mpi)
            }
            LookupResult::Parent(None) => panic!("should have move path for every Local"),
        }
    }

    fn move_path_for_place(&mut self, place: PlaceRef<'tcx>) -> Option<MovePathIndex> {
        // If returns None, then there is no move path corresponding
        // to a direct owner of `place` (which means there is nothing
        // that borrowck tracks for its analysis).

        match self.move_data.rev_lookup.find(place) {
            LookupResult::Parent(_) => None,
            LookupResult::Exact(mpi) => Some(mpi),
        }
    }

    fn is_local_ever_initialized(
        &self,
        local: Local,
        state: &BorrowckDomain<'a, 'tcx>,
    ) -> Option<InitIndex> {
        let mpi = self.move_data.rev_lookup.find_local(local)?;
        let ii = &self.move_data.init_path_map[mpi];
        ii.into_iter().find(|&&index| state.ever_inits.contains(index)).copied()
    }

    /// Adds the place into the used mutable variables set
    fn add_used_mut(&mut self, root_place: RootPlace<'tcx>, state: &BorrowckDomain<'a, 'tcx>) {
        match root_place {
            RootPlace { place_local: local, place_projection: [], is_local_mutation_allowed } => {
                // If the local may have been initialized, and it is now currently being
                // mutated, then it is justified to be annotated with the `mut`
                // keyword, since the mutation may be a possible reassignment.
                if is_local_mutation_allowed != LocalMutationIsAllowed::Yes
                    && self.is_local_ever_initialized(local, state).is_some()
                {
                    self.used_mut.insert(local);
                }
            }
            RootPlace {
                place_local: _,
                place_projection: _,
                is_local_mutation_allowed: LocalMutationIsAllowed::Yes,
            } => {}
            RootPlace {
                place_local,
                place_projection: place_projection @ [.., _],
                is_local_mutation_allowed: _,
            } => {
                if let Some(field) = self.is_upvar_field_projection(PlaceRef {
                    local: place_local,
                    projection: place_projection,
                }) {
                    self.used_mut_upvars.push(field);
                }
            }
        }
    }

    /// Whether this value can be written or borrowed mutably.
    /// Returns the root place if the place passed in is a projection.
    #[allow(unreachable_code)]
    fn is_mutable(
        &self,
        place: PlaceRef<'tcx>,
        is_local_mutation_allowed: LocalMutationIsAllowed,
    ) -> Result<RootPlace<'tcx>, PlaceRef<'tcx>> {
        return Ok(RootPlace {
            place_local: place.local,
            place_projection: place.projection,
            is_local_mutation_allowed: LocalMutationIsAllowed::Yes,
        });

        debug!("is_mutable: place={:?}, is_local...={:?}", place, is_local_mutation_allowed);
        match place.last_projection() {
            None => {
                let local = &self.body.local_decls[place.local];
                match local.mutability {
                    Mutability::Not => match is_local_mutation_allowed {
                        LocalMutationIsAllowed::Yes => Ok(RootPlace {
                            place_local: place.local,
                            place_projection: place.projection,
                            is_local_mutation_allowed: LocalMutationIsAllowed::Yes,
                        }),
                        LocalMutationIsAllowed::ExceptUpvars => Ok(RootPlace {
                            place_local: place.local,
                            place_projection: place.projection,
                            is_local_mutation_allowed: LocalMutationIsAllowed::ExceptUpvars,
                        }),
                        LocalMutationIsAllowed::No => Err(place),
                    },
                    Mutability::Mut => Ok(RootPlace {
                        place_local: place.local,
                        place_projection: place.projection,
                        is_local_mutation_allowed,
                    }),
                }
            }
            Some((place_base, elem)) => {
                match elem {
                    ProjectionElem::Deref => {
                        let base_ty = place_base.ty(self.body(), self.infcx.tcx).ty;

                        // Check the kind of deref to decide
                        match base_ty.kind() {
                            ty::Ref(_, _, mutbl) => {
                                match mutbl {
                                    // Shared borrowed data is never mutable
                                    hir::Mutability::Not => Err(place),
                                    // Mutably borrowed data is mutable, but only if we have a
                                    // unique path to the `&mut`
                                    hir::Mutability::Mut => {
                                        let mode = match self.is_upvar_field_projection(place) {
                                            Some(field)
                                                if self.upvars[field.index()].is_by_ref() =>
                                            {
                                                is_local_mutation_allowed
                                            }
                                            _ => LocalMutationIsAllowed::Yes,
                                        };

                                        self.is_mutable(place_base, mode)
                                    }
                                }
                            }
                            ty::RawPtr(_, mutbl) => {
                                match mutbl {
                                    // `*const` raw pointers are not mutable
                                    hir::Mutability::Not => Err(place),
                                    // `*mut` raw pointers are always mutable, regardless of
                                    // context. The users have to check by themselves.
                                    hir::Mutability::Mut => Ok(RootPlace {
                                        place_local: place.local,
                                        place_projection: place.projection,
                                        is_local_mutation_allowed,
                                    }),
                                }
                            }
                            // `Box<T>` owns its content, so mutable if its location is mutable
                            _ if base_ty.is_box() => {
                                self.is_mutable(place_base, is_local_mutation_allowed)
                            }
                            // Deref should only be for reference, pointers or boxes
                            _ => bug!("Deref of unexpected type: {:?}", base_ty),
                        }
                    }
                    // All other projections are owned by their base path, so mutable if
                    // base path is mutable
                    ProjectionElem::Field(..)
                    | ProjectionElem::Index(..)
                    | ProjectionElem::ConstantIndex { .. }
                    | ProjectionElem::Subslice { .. }
                    | ProjectionElem::Subtype(..)
                    | ProjectionElem::OpaqueCast { .. }
                    | ProjectionElem::Downcast(..) => {
                        let upvar_field_projection = self.is_upvar_field_projection(place);
                        if let Some(field) = upvar_field_projection {
                            let upvar = &self.upvars[field.index()];
                            debug!(
                                "is_mutable: upvar.mutability={:?} local_mutation_is_allowed={:?} \
                                 place={:?}, place_base={:?}",
                                upvar, is_local_mutation_allowed, place, place_base
                            );
                            match (upvar.mutability, is_local_mutation_allowed) {
                                (
                                    Mutability::Not,
                                    LocalMutationIsAllowed::No
                                    | LocalMutationIsAllowed::ExceptUpvars,
                                ) => Err(place),
                                (Mutability::Not, LocalMutationIsAllowed::Yes)
                                | (Mutability::Mut, _) => {
                                    // Subtle: this is an upvar
                                    // reference, so it looks like
                                    // `self.foo` -- we want to double
                                    // check that the location `*self`
                                    // is mutable (i.e., this is not a
                                    // `Fn` closure). But if that
                                    // check succeeds, we want to
                                    // *blame* the mutability on
                                    // `place` (that is,
                                    // `self.foo`). This is used to
                                    // propagate the info about
                                    // whether mutability declarations
                                    // are used outwards, so that we register
                                    // the outer variable as mutable. Otherwise a
                                    // test like this fails to record the `mut`
                                    // as needed:
                                    //
                                    // ```
                                    // fn foo<F: FnOnce()>(_f: F) { }
                                    // fn main() {
                                    //     let var = Vec::new();
                                    //     foo(move || {
                                    //         var.push(1);
                                    //     });
                                    // }
                                    // ```
                                    // let _ =
                                    //     self.is_mutable(place_base, is_local_mutation_allowed)?;
                                    Ok(RootPlace {
                                        place_local: place.local,
                                        place_projection: place.projection,
                                        is_local_mutation_allowed,
                                    })
                                }
                            }
                        } else {
                            self.is_mutable(place_base, is_local_mutation_allowed)
                        }
                    }
                }
            }
        }
    }

    /// If `place` is a field projection, and the field is being projected from a closure type,
    /// then returns the index of the field being projected. Note that this closure will always
    /// be `self` in the current MIR, because that is the only time we directly access the fields
    /// of a closure type.
    fn is_upvar_field_projection(&self, place_ref: PlaceRef<'tcx>) -> Option<FieldIdx> {
        path_utils::is_upvar_field_projection(self.infcx.tcx, &self.upvars, place_ref, self.body())
    }

    fn dominators(&self) -> &Dominators<BasicBlock> {
        // `BasicBlocks` computes dominators on-demand and caches them.
        self.body.basic_blocks.dominators()
    }
}

mod diags {
    use rustc_errors::ErrorGuaranteed;

    use super::*;

    enum BufferedDiag<'infcx> {
        Error(Diag<'infcx>),
        NonError(Diag<'infcx, ()>),
    }

    impl<'infcx> BufferedDiag<'infcx> {
        fn sort_span(&self) -> Span {
            match self {
                BufferedDiag::Error(diag) => diag.sort_span,
                BufferedDiag::NonError(diag) => diag.sort_span,
            }
        }
    }

    pub(crate) struct BorrowckDiags<'infcx, 'tcx> {
        /// This field keeps track of move errors that are to be reported for given move indices.
        ///
        /// There are situations where many errors can be reported for a single move out (see
        /// #53807) and we want only the best of those errors.
        ///
        /// The `report_use_of_moved_or_uninitialized` function checks this map and replaces the
        /// diagnostic (if there is one) if the `Place` of the error being reported is a prefix of
        /// the `Place` of the previous most diagnostic. This happens instead of buffering the
        /// error. Once all move errors have been reported, any diagnostics in this map are added
        /// to the buffer to be emitted.
        ///
        /// `BTreeMap` is used to preserve the order of insertions when iterating. This is necessary
        /// when errors in the map are being re-added to the error buffer so that errors with the
        /// same primary span come out in a consistent order.
        buffered_move_errors: BTreeMap<Vec<MoveOutIndex>, (PlaceRef<'tcx>, Diag<'infcx>)>,

        buffered_mut_errors: FxIndexMap<Span, (Diag<'infcx>, usize)>,

        /// Buffer of diagnostics to be reported. A mixture of error and non-error diagnostics.
        buffered_diags: Vec<BufferedDiag<'infcx>>,
    }

    impl<'infcx, 'tcx> BorrowckDiags<'infcx, 'tcx> {
        pub(crate) fn new() -> Self {
            BorrowckDiags {
                buffered_move_errors: BTreeMap::new(),
                buffered_mut_errors: Default::default(),
                buffered_diags: Default::default(),
            }
        }

        pub(crate) fn buffer_error(&mut self, diag: Diag<'infcx>) {
            self.buffered_diags.push(BufferedDiag::Error(diag));
        }

        pub(crate) fn buffer_non_error(&mut self, diag: Diag<'infcx, ()>) {
            self.buffered_diags.push(BufferedDiag::NonError(diag));
        }
    }

    impl<'infcx, 'tcx> MirBorrowckCtxt<'_, 'infcx, 'tcx> {
        pub(crate) fn buffer_error(&mut self, diag: Diag<'infcx>) {
            self.diags.buffer_error(diag);
        }

        pub(crate) fn buffer_non_error(&mut self, diag: Diag<'infcx, ()>) {
            self.diags.buffer_non_error(diag);
        }

        pub(crate) fn buffer_move_error(
            &mut self,
            move_out_indices: Vec<MoveOutIndex>,
            place_and_err: (PlaceRef<'tcx>, Diag<'infcx>),
        ) -> bool {
            if let Some((_, diag)) =
                self.diags.buffered_move_errors.insert(move_out_indices, place_and_err)
            {
                // Cancel the old diagnostic so we don't ICE
                diag.cancel();
                false
            } else {
                true
            }
        }

        pub(crate) fn get_buffered_mut_error(
            &mut self,
            span: Span,
        ) -> Option<(Diag<'infcx>, usize)> {
            // FIXME(#120456) - is `swap_remove` correct?
            self.diags.buffered_mut_errors.swap_remove(&span)
        }

        pub(crate) fn buffer_mut_error(&mut self, span: Span, diag: Diag<'infcx>, count: usize) {
            self.diags.buffered_mut_errors.insert(span, (diag, count));
        }

        pub(crate) fn emit_errors(&mut self) -> Option<ErrorGuaranteed> {
            let mut res = self.infcx.tainted_by_errors();

            // Buffer any move errors that we collected and de-duplicated.
            for (_, (_, diag)) in std::mem::take(&mut self.diags.buffered_move_errors) {
                // We have already set tainted for this error, so just buffer it.
                self.diags.buffered_diags.push(BufferedDiag::Error(diag));
            }
            for (_, (mut diag, count)) in std::mem::take(&mut self.diags.buffered_mut_errors) {
                if count > 10 {
                    #[allow(rustc::diagnostic_outside_of_impl)]
                    #[allow(rustc::untranslatable_diagnostic)]
                    diag.note(format!("...and {} other attempted mutable borrows", count - 10));
                }
                self.diags.buffered_diags.push(BufferedDiag::Error(diag));
            }

            if !self.diags.buffered_diags.is_empty() {
                self.diags.buffered_diags.sort_by_key(|buffered_diag| buffered_diag.sort_span());
                for buffered_diag in self.diags.buffered_diags.drain(..) {
                    match buffered_diag {
                        BufferedDiag::Error(diag) => res = Some(diag.emit()),
                        BufferedDiag::NonError(diag) => diag.emit(),
                    }
                }
            }

            res
        }

        pub(crate) fn has_buffered_diags(&self) -> bool {
            self.diags.buffered_diags.is_empty()
        }

        pub(crate) fn has_move_error(
            &self,
            move_out_indices: &[MoveOutIndex],
        ) -> Option<&(PlaceRef<'tcx>, Diag<'infcx>)> {
            self.diags.buffered_move_errors.get(move_out_indices)
        }
    }
}

/// The degree of overlap between 2 places for borrow-checking.
enum Overlap {
    /// The places might partially overlap - in this case, we give
    /// up and say that they might conflict. This occurs when
    /// different fields of a union are borrowed. For example,
    /// if `u` is a union, we have no way of telling how disjoint
    /// `u.a.x` and `a.b.y` are.
    Arbitrary,
    /// The places have the same type, and are either completely disjoint
    /// or equal - i.e., they can't "partially" overlap as can occur with
    /// unions. This is the "base case" on which we recur for extensions
    /// of the place.
    EqualOrDisjoint,
    /// The places are disjoint, so we know all extensions of them
    /// will also be disjoint.
    Disjoint,
}
