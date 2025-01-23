/*! `ocaml` grammar compiled for Highlight.js 11.10.0 */
  (function(){
    var hljsGrammar = (function () {
  'use strict';

  function fstar(hljs) {
    /* missing support for heredoc-like string (OCaml 4.0.2+) */
    return {
        name: 'FStar',
        aliases: [ 'fstar', 'fst', 'fsti' ],
      keywords: {
        $pattern: '[a-z_]\\w*!?',
        keyword: 'attributes noeq unopteq and assert assume begin by calc class default decreases effect eliminate else end ensures exception exists false friend forall fun λ function if in include inline inline_for_extraction instance introduce irreducible let logic match returns as module new new_effect layered_effect polymonadic_bind polymonadic_subcomp noextract of open opaque private quote range_of rec reifiable reify reflectable requires set_range_of sub_effect synth then total true try type unfold unfoldable val when with string',
        built_in: 'unit',
        literal: 'true false'
      },
      // illegal: /\/\/|>>/,
      contains: [
        {
          className: 'literal',
          begin: '\\[(\\|\\|)?\\]|\\(\\)',
          relevance: 0
        },
        hljs.COMMENT(
          '\\(\\*',
          '\\*\\)',
          { contains: [ 'self' ] }
        ),
        //   hljs.inherit(
        //       hljs.COMMENT(),
        //       {
        //           match: [
        //               /(^|\s)/,
        //               /\/\/.*$/
        //           ],
        //           scope: {
        //               2: 'comment'
        //           }
        //       }
        //   ),
        { /* type variable */
          className: 'symbol',
          begin: '\'[A-Za-z_](?!\')[\\w\']*'
          /* the grammar is ambiguous on how 'a'b should be interpreted but not the compiler */
        },
        { /* module or constructor */
          className: 'type',
          begin: '\\b[A-Z][\\w\']*',
          relevance: 0
        },
        { /* don't color identifiers, but safely catch all identifiers with ' */
          begin: '[a-z_]\\w*\'[\\w\']*',
          relevance: 0
        },
        hljs.inherit(hljs.APOS_STRING_MODE, {
          className: 'string',
          relevance: 0
        }),
        hljs.inherit(hljs.QUOTE_STRING_MODE, { illegal: null }),
        {
          className: 'number',
          begin:
            '\\b(0[xX][a-fA-F0-9_]+[Lln]?|'
            + '0[oO][0-7_]+[Lln]?|'
            + '0[bB][01_]+[Lln]?|'
            + '[0-9][0-9_]*([Lln]|(\\.[0-9_]*)?([eE][-+]?[0-9_]+)?)?)',
          relevance: 0
        },
        { begin: /->/ // relevance booster
        }
      ]
    };
  }

  return fstar;

})();
    hljs.registerLanguage('fstar', hljsGrammar);
  })();

// hljs.initHighlightingOnLoad();

