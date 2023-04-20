use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{
    interface::{self, Compiler},
    Queries,
};

pub(crate) struct LinterCallbacks {}

impl Callbacks for LinterCallbacks {
    fn after_parsing<'tcx>(
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
        let session = compiler.session();
        queries
            .global_ctxt()
            .unwrap()
            .peek_mut()
            .enter(|tcx| circus_lint::Linter::register(tcx, session));

        Compilation::Continue
    }
}
