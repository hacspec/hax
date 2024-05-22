use const_format::formatcp;
use hax_cli_options::{Command, ENV_VAR_OPTIONS_FRONTEND};

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{interface, Queries};
use rustc_span::symbol::Symbol;

/// Wraps a [Callbacks] structure, and injects some cache-related
/// configuration in the `config` phase of rustc
pub struct CallbacksWrapper<'a> {
    pub sub: &'a mut (dyn Callbacks + Send + 'a),
    pub options: hax_cli_options::Options,
}
impl<'a> Callbacks for CallbacksWrapper<'a> {
    fn config(&mut self, config: &mut interface::Config) {
        let options = self.options.clone();
        config.parse_sess_created = Some(Box::new(move |parse_sess| {
            parse_sess.env_depinfo.get_mut().insert((
                Symbol::intern(hax_cli_options::ENV_VAR_OPTIONS_FRONTEND),
                Some(Symbol::intern(&serde_json::to_string(&options).unwrap())),
            ));
        }));
        self.sub.config(config)
    }
    fn after_parsing<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        self.sub.after_parsing(compiler, queries)
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
        early_handler: &rustc_session::EarlyErrorHandler,
        compiler: &interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        self.sub.after_analysis(early_handler, compiler, queries)
    }
}
