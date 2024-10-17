#![allow(rustc::diagnostic_outside_of_impl)]
#![allow(rustc::untranslatable_diagnostic)]

use rustc_errors::{Applicability, Diag};
use rustc_hir::intravisit::Visitor;
use rustc_hir::{CaptureBy, ExprKind, HirId, Node};
use rustc_middle::bug;
use rustc_middle::mir::*;
use rustc_middle::ty::{self, Ty};
use rustc_mir_dataflow::move_paths::{LookupResult, MovePathIndex};
use rustc_span::{BytePos, ExpnKind, MacroKind, Span};
use rustc_trait_selection::error_reporting::traits::FindExprBySpan;
use tracing::debug;

use crate::MirBorrowckCtxt;
use crate::diagnostics::{CapturedMessageOpt, DescribePlaceOpt, UseSpans};
use crate::prefixes::PrefixSet;

#[derive(Debug)]
pub(crate) enum IllegalMoveOriginKind<'tcx> {
    /// Illegal move due to attempt to move from behind a reference.
    BorrowedContent {
        /// The place the reference refers to: if erroneous code was trying to
        /// move from `(*x).f` this will be `*x`.
        target_place: Place<'tcx>,
    },

    /// Illegal move due to attempt to move from field of an ADT that
    /// implements `Drop`. Rust maintains invariant that all `Drop`
    /// ADT's remain fully-initialized so that user-defined destructor
    /// can safely read from all of the ADT's fields.
    InteriorOfTypeWithDestructor { container_ty: Ty<'tcx> },

    /// Illegal move due to attempt to move out of a slice or array.
    InteriorOfSliceOrArray { ty: Ty<'tcx>, is_index: bool },
}

#[derive(Debug)]
pub(crate) struct MoveError<'tcx> {
    place: Place<'tcx>,
    location: Location,
    kind: IllegalMoveOriginKind<'tcx>,
}

impl<'tcx> MoveError<'tcx> {
    pub(crate) fn new(
        place: Place<'tcx>,
        location: Location,
        kind: IllegalMoveOriginKind<'tcx>,
    ) -> Self {
        MoveError { place, location, kind }
    }
}

// Often when desugaring a pattern match we may have many individual moves in
// MIR that are all part of one operation from the user's point-of-view. For
// example:
//
// let (x, y) = foo()
//
// would move x from the 0 field of some temporary, and y from the 1 field. We
// group such errors together for cleaner error reporting.
//
// Errors are kept separate if they are from places with different parent move
// paths. For example, this generates two errors:
//
// let (&x, &y) = (&String::new(), &String::new());
#[derive(Debug)]
enum GroupedMoveError<'tcx> {
    // Place expression can't be moved from,
    // e.g., match x[0] { s => (), } where x: &[String]
    MovesFromPlace {
        original_path: Place<'tcx>,
        span: Span,
        move_from: Place<'tcx>,
        kind: IllegalMoveOriginKind<'tcx>,
        binds_to: Vec<Local>,
    },
    // Part of a value expression can't be moved from,
    // e.g., match &String::new() { &x => (), }
    MovesFromValue {
        original_path: Place<'tcx>,
        span: Span,
        move_from: MovePathIndex,
        kind: IllegalMoveOriginKind<'tcx>,
        binds_to: Vec<Local>,
    },
    // Everything that isn't from pattern matching.
    OtherIllegalMove {
        original_path: Place<'tcx>,
        use_spans: UseSpans<'tcx>,
        kind: IllegalMoveOriginKind<'tcx>,
    },
}

impl<'infcx, 'tcx> MirBorrowckCtxt<'_, 'infcx, 'tcx> {
    pub(crate) fn report_move_errors(&mut self) {
        let grouped_errors = self.group_move_errors();
        for error in grouped_errors {
            self.report(error);
        }
    }

    fn group_move_errors(&mut self) -> Vec<GroupedMoveError<'tcx>> {
        let mut grouped_errors = Vec::new();
        let errors = std::mem::take(&mut self.move_errors);
        for error in errors {
            self.append_to_grouped_errors(&mut grouped_errors, error);
        }
        grouped_errors
    }

    fn append_to_grouped_errors(
        &self,
        grouped_errors: &mut Vec<GroupedMoveError<'tcx>>,
        error: MoveError<'tcx>,
    ) {
        let MoveError { place: original_path, location, kind } = error;

        // Note: that the only time we assign a place isn't a temporary
        // to a user variable is when initializing it.
        // If that ever stops being the case, then the ever initialized
        // flow could be used.
        if let Some(StatementKind::Assign(box (place, Rvalue::Use(Operand::Move(move_from))))) =
            self.body.basic_blocks[location.block]
                .statements
                .get(location.statement_index)
                .map(|stmt| &stmt.kind)
        {
            if let Some(local) = place.as_local() {
                let local_decl = &self.body.local_decls[local];
                // opt_match_place is the
                // match_span is the span of the expression being matched on
                // match *x.y { ... }        match_place is Some(*x.y)
                //       ^^^^                match_span is the span of *x.y
                //
                // opt_match_place is None for let [mut] x = ... statements,
                // whether or not the right-hand side is a place expression
                if let LocalInfo::User(BindingForm::Var(VarBindingForm {
                    opt_match_place: Some((opt_match_place, match_span)),
                    binding_mode: _,
                    opt_ty_info: _,
                    pat_span: _,
                })) = *local_decl.local_info()
                {
                    let stmt_source_info = self.body.source_info(location);
                    self.append_binding_error(
                        grouped_errors,
                        kind,
                        original_path,
                        *move_from,
                        local,
                        opt_match_place,
                        match_span,
                        stmt_source_info.span,
                    );
                    return;
                }
            }
        }

        let move_spans = self.move_spans(original_path.as_ref(), location);
        grouped_errors.push(GroupedMoveError::OtherIllegalMove {
            use_spans: move_spans,
            original_path,
            kind,
        });
    }

    fn append_binding_error(
        &self,
        grouped_errors: &mut Vec<GroupedMoveError<'tcx>>,
        kind: IllegalMoveOriginKind<'tcx>,
        original_path: Place<'tcx>,
        move_from: Place<'tcx>,
        bind_to: Local,
        match_place: Option<Place<'tcx>>,
        match_span: Span,
        statement_span: Span,
    ) {
        debug!(?match_place, ?match_span, "append_binding_error");

        let from_simple_let = match_place.is_none();
        let match_place = match_place.unwrap_or(move_from);

        match self.move_data.rev_lookup.find(match_place.as_ref()) {
            // Error with the match place
            LookupResult::Parent(_) => {
                for ge in &mut *grouped_errors {
                    if let GroupedMoveError::MovesFromPlace { span, binds_to, .. } = ge
                        && match_span == *span
                    {
                        debug!("appending local({bind_to:?}) to list");
                        if !binds_to.is_empty() {
                            binds_to.push(bind_to);
                        }
                        return;
                    }
                }
                debug!("found a new move error location");

                // Don't need to point to x in let x = ... .
                let (binds_to, span) = if from_simple_let {
                    (vec![], statement_span)
                } else {
                    (vec![bind_to], match_span)
                };
                grouped_errors.push(GroupedMoveError::MovesFromPlace {
                    span,
                    move_from,
                    original_path,
                    kind,
                    binds_to,
                });
            }
            // Error with the pattern
            LookupResult::Exact(_) => {
                let LookupResult::Parent(Some(mpi)) =
                    self.move_data.rev_lookup.find(move_from.as_ref())
                else {
                    // move_from should be a projection from match_place.
                    unreachable!("Probably not unreachable...");
                };
                for ge in &mut *grouped_errors {
                    if let GroupedMoveError::MovesFromValue {
                        span,
                        move_from: other_mpi,
                        binds_to,
                        ..
                    } = ge
                    {
                        if match_span == *span && mpi == *other_mpi {
                            debug!("appending local({bind_to:?}) to list");
                            binds_to.push(bind_to);
                            return;
                        }
                    }
                }
                debug!("found a new move error location");
                grouped_errors.push(GroupedMoveError::MovesFromValue {
                    span: match_span,
                    move_from: mpi,
                    original_path,
                    kind,
                    binds_to: vec![bind_to],
                });
            }
        };
    }

    fn report(&mut self, _error: GroupedMoveError<'tcx>) {
    }
}
