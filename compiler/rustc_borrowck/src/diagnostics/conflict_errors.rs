// ignore-tidy-filelength

#![allow(rustc::diagnostic_outside_of_impl)]
#![allow(rustc::untranslatable_diagnostic)]

use std::iter;
use std::ops::ControlFlow;

use either::Either;
use hir::{ClosureKind, Path};
use rustc_data_structures::captures::Captures;
use rustc_data_structures::fx::FxIndexSet;
use rustc_errors::codes::*;
use rustc_errors::{Applicability, Diag, MultiSpan, struct_span_code_err};
use rustc_hir as hir;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::intravisit::{Map, Visitor, walk_block, walk_expr};
use rustc_hir::{CoroutineDesugaring, CoroutineKind, CoroutineSource, LangItem, PatField};
use rustc_middle::bug;
use rustc_middle::hir::nested_filter::OnlyBodies;
use rustc_middle::mir::tcx::PlaceTy;
use rustc_middle::mir::{
    self, AggregateKind, BindingForm, BorrowKind, CallSource, ClearCrossCrate, ConstraintCategory,
    FakeBorrowKind, FakeReadCause, LocalDecl, LocalInfo, LocalKind, Location, MutBorrowKind,
    Operand, Place, PlaceRef, ProjectionElem, Rvalue, Statement, StatementKind, Terminator,
    TerminatorKind, VarBindingForm, VarDebugInfoContents,
};
use rustc_middle::ty::print::PrintTraitRefExt as _;
use rustc_middle::ty::{
    self, PredicateKind, Ty, TyCtxt, TypeSuperVisitable, TypeVisitor, Upcast,
    suggest_constraining_type_params,
};
use rustc_middle::util::CallKind;
use rustc_mir_dataflow::move_paths::{InitKind, MoveOutIndex, MovePathIndex};
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_span::hygiene::DesugaringKind;
use rustc_span::symbol::{Ident, kw, sym};
use rustc_span::{BytePos, Span, Symbol};
use rustc_trait_selection::error_reporting::InferCtxtErrorExt;
use rustc_trait_selection::error_reporting::traits::FindExprBySpan;
use rustc_trait_selection::infer::InferCtxtExt;
use rustc_trait_selection::traits::{Obligation, ObligationCause, ObligationCtxt};
use tracing::{debug, instrument};

use super::explain_borrow::{BorrowExplanation, LaterUseKind};
use super::{DescribePlaceOpt, RegionName, RegionNameSource, UseSpans};
use crate::borrow_set::{BorrowData, TwoPhaseActivation};
use crate::diagnostics::conflict_errors::StorageDeadOrDrop::LocalStorageDead;
use crate::diagnostics::{CapturedMessageOpt, Instance, find_all_local_uses};
use crate::prefixes::IsPrefixOf;
use crate::{InitializationRequiringAction, MirBorrowckCtxt, WriteKind, borrowck_errors};

#[derive(Debug)]
struct MoveSite {
    /// Index of the "move out" that we found. The `MoveData` can
    /// then tell us where the move occurred.
    moi: MoveOutIndex,

    /// `true` if we traversed a back edge while walking from the point
    /// of error to the move site.
    traversed_back_edge: bool,
}

/// Which case a StorageDeadOrDrop is for.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum StorageDeadOrDrop<'tcx> {
    LocalStorageDead,
    BoxedStorageDead,
    Destructor(Ty<'tcx>),
}

impl<'infcx, 'tcx> MirBorrowckCtxt<'_, 'infcx, 'tcx> {
}
