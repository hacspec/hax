use hax_types::cli_options::{Command, Options, ENV_VAR_OPTIONS_FRONTEND};

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{interface, Queries};
use rustc_span::symbol::Symbol;

/// Wraps a [Callbacks] structure, and injects some cache-related
/// configuration in the `config` phase of rustc
pub struct CallbacksWrapper<'a> {
    pub sub: &'a mut (dyn Callbacks + Send + 'a),
    pub options: Options,
}
impl<'a> Callbacks for CallbacksWrapper<'a> {
    fn config(&mut self, config: &mut interface::Config) {
        let options = self.options.clone();
        config.psess_created = Some(Box::new(move |parse_sess| {
            parse_sess.env_depinfo.get_mut().insert((
                Symbol::intern(ENV_VAR_OPTIONS_FRONTEND),
                Some(Symbol::intern(&serde_json::to_string(&options).unwrap())),
            ));
        }));
        self.sub.config(config)
    }
    fn after_crate_root_parsing<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        self.sub.after_crate_root_parsing(compiler, queries)
    }
    fn after_expansion<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        self.sub.after_expansion(compiler, queries)
    }
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        self.sub.after_analysis(compiler, queries)
    }
}
