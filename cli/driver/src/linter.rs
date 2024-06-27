use hax_lint::Type;
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{
    interface::{self, Compiler},
    Queries,
};

pub(crate) struct LinterCallbacks {
    ltype: Type,
}

impl LinterCallbacks {
    pub(crate) fn new(ltype: Type) -> Self {
        Self { ltype }
    }
}

impl Callbacks for LinterCallbacks {
    fn after_crate_root_parsing<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        Compilation::Continue
    }
    fn after_expansion<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        queries
            .global_ctxt()
            .unwrap()
            .enter(|tcx| hax_lint::Linter::register(tcx, self.ltype));

        Compilation::Continue
    }
}
