use rustc_borrowck::consumers::{
    BodyWithBorrowckFacts, ConsumerOptions, get_bodies_with_borrowck_facts,
};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;
use rustc_utils::cache::Cache;

thread_local! {
    static BODIES_WITH_FACTS: Cache<LocalDefId, BodyWithBorrowckFacts<'static>> = Cache::default();
}

pub(crate) fn record<'tcx>(tcx: TyCtxt<'tcx>, root: LocalDefId) {
    for (def, body_with_facts) in
        get_bodies_with_borrowck_facts(tcx, root, ConsumerOptions::PoloniusInputFacts)
    {
        // SAFETY: rustc starts a fresh compiler thread for each session, so this
        // thread-local cache never outlives the arena the facts point into.
        let body_with_facts: BodyWithBorrowckFacts<'static> = unsafe {
            std::mem::transmute::<BodyWithBorrowckFacts<'tcx>, BodyWithBorrowckFacts<'static>>(
                body_with_facts,
            )
        };
        BODIES_WITH_FACTS.with(|cache| {
            cache.get(&def, |_| body_with_facts);
        });
    }
}

// The facts the borrow checker of rustc computed for a local body.
// Needs `driver::record_borrowck_facts`.
pub fn borrowck_facts<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
) -> &'tcx BodyWithBorrowckFacts<'tcx> {
    let _ = tcx.mir_borrowck(tcx.typeck_root_def_id_local(def));
    BODIES_WITH_FACTS.with(|cache| {
        let body_with_facts: &BodyWithBorrowckFacts<'static> = cache.get(&def, |_| {
            panic!("driver::record_borrowck_facts records the facts of every local body")
        });
        // SAFETY: the cache pins its entries for the whole session of this thread.
        unsafe {
            std::mem::transmute::<&BodyWithBorrowckFacts<'static>, &'tcx BodyWithBorrowckFacts<'tcx>>(
                body_with_facts,
            )
        }
    })
}
