use rustc_middle::mir::{BasicBlock, Body, TerminatorKind};
use rustc_middle::ty::TyCtxt;
use rustc_mir_dataflow::impls::MaybeInitializedPlaces;
use rustc_mir_dataflow::move_paths::{LookupResult, MoveData};
use rustc_mir_dataflow::{Analysis, ResultsCursor};

// rustc builds a `Drop` for every value that may need one and removes those of a place
// that is moved out on every path to them in drop elaboration, after the borrow check.
// The recorded MIR comes before that pass, so they are removed here.
pub(crate) fn remove_dead_drops<'tcx>(tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
    for (block, target) in dead_drops(tcx, body) {
        body.basic_blocks_mut()[block].terminator_mut().kind = TerminatorKind::Goto { target };
    }
}

// The block of each dead `Drop` and the block it continues to.
fn dead_drops<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Vec<(BasicBlock, BasicBlock)> {
    let move_data: MoveData<'tcx> = MoveData::gather_moves(body, tcx, |_| true);
    let mut maybe_initialized: ResultsCursor<'_, 'tcx, MaybeInitializedPlaces<'_, 'tcx>> =
        MaybeInitializedPlaces::new(tcx, body, &move_data)
            .iterate_to_fixpoint(tcx, body, None)
            .into_results_cursor(body);
    body.basic_blocks
        .iter_enumerated()
        .filter_map(|(block, data)| {
            let TerminatorKind::Drop { place, target, .. } = data.terminator().kind else {
                return None;
            };
            maybe_initialized.seek_before_primary_effect(body.terminator_loc(block));
            match move_data.rev_lookup.find(place.as_ref()) {
                LookupResult::Exact(path) if !maybe_initialized.get().contains(path) => {
                    Some((block, target))
                }
                LookupResult::Exact(_) | LookupResult::Parent(_) => None,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use rustc_hir::def_id::LocalDefId;
    use rustc_middle::mir::TerminatorKind;
    use rustc_middle::ty::TyCtxt;

    use crate::recorded_mir;
    use crate::test_utils::Compile;

    fn drops_in_f(source: &str) -> usize {
        let mut drops: Option<usize> = None;
        Compile::source(source).run(|tcx: TyCtxt<'_>| {
            let f: LocalDefId = tcx
                .hir_body_owners()
                .find(|&owner| tcx.def_path_str(owner) == "f")
                .expect("the source defines f");
            let (body, _) =
                &recorded_mir(tcx, f.to_def_id()).expect("f is recorded").bodies[&f.to_def_id()];
            drops = Some(
                body.basic_blocks
                    .iter()
                    .filter(|data| matches!(data.terminator().kind, TerminatorKind::Drop { .. }))
                    .count(),
            );
        });
        drops.expect("the compilation records f")
    }

    #[test]
    fn a_drop_of_a_value_stays() {
        assert_eq!(drops_in_f("pub fn f(s: String) {}"), 1);
    }

    #[test]
    fn a_drop_of_a_moved_out_value_is_removed() {
        assert_eq!(drops_in_f("pub fn f(s: String) -> String { s }"), 0);
    }

    #[test]
    fn a_drop_of_a_value_moved_out_on_one_path_stays() {
        assert_eq!(
            drops_in_f(
                "pub fn f(s: String, b: bool) -> Option<String> { if b { Some(s) } else { None } }"
            ),
            1
        );
    }
}
