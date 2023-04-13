type token =
    AMP
  | AND
  | AND_OP of Prims.string
  | AS
  | ASSERT
  | ASSUME
  | ATTRIBUTES
  | BACKTICK
  | BACKTICK_AT
  | BACKTICK_HASH
  | BACKTICK_PERC
  | BANG_LBRACE
  | BAR
  | BAR_RBRACE
  | BAR_RBRACK
  | BEGIN
  | BY
  | CALC
  | CHAR of FStar_String.char
  | CLASS
  | COLON
  | COLON_COLON
  | COLON_EQUALS
  | COMMA
  | CONJUNCTION
  | DECREASES
  | DEFAULT
  | DISJUNCTION
  | DOLLAR
  | DOT
  | DOT_LBRACK
  | DOT_LBRACK_BAR
  | DOT_LENS_PAREN_LEFT
  | DOT_LPAREN
  | EFFECT
  | ELIM
  | ELSE
  | END
  | ENSURES
  | EOF
  | EQUALS
  | EQUALTYPE
  | EXCEPTION
  | EXISTS
  | FALSE
  | FORALL
  | FRIEND
  | FUN
  | FUNCTION
  | HASH
  | IDENT of Prims.string
  | IF
  | IFF
  | IF_OP of Prims.string
  | IMPLIES
  | IN
  | INCLUDE
  | INLINE
  | INLINE_FOR_EXTRACTION
  | INSTANCE
  | INT of (Prims.string * Prims.bool)
  | INT16 of (Prims.string * Prims.bool)
  | INT32 of (Prims.string * Prims.bool)
  | INT64 of (Prims.string * Prims.bool)
  | INT8 of (Prims.string * Prims.bool)
  | INTRO
  | IRREDUCIBLE
  | LARROW
  | LAYERED_EFFECT
  | LBRACE
  | LBRACE_BAR
  | LBRACE_COLON_PATTERN
  | LBRACE_COLON_WELL_FOUNDED
  | LBRACK
  | LBRACK_AT
  | LBRACK_AT_AT
  | LBRACK_AT_AT_AT
  | LBRACK_BAR
  | LENS_PAREN_LEFT
  | LENS_PAREN_RIGHT
  | LET of Prims.bool
  | LET_OP of Prims.string
  | LOGIC
  | LONG_LEFT_ARROW
  | LPAREN
  | LPAREN_RPAREN
  | MATCH
  | MATCH_OP of Prims.string
  | MINUS
  | MODULE
  | NAME of Prims.string
  | NEW
  | NEW_EFFECT
  | NOEQUALITY
  | NOEXTRACT
  | OF
  | OPAQUE
  | OPEN
  | OPINFIX0a of Prims.string
  | OPINFIX0b of Prims.string
  | OPINFIX0c of Prims.string
  | OPINFIX0d of Prims.string
  | OPINFIX1 of Prims.string
  | OPINFIX2 of Prims.string
  | OPINFIX3 of Prims.string
  | OPINFIX4 of Prims.string
  | OPPREFIX of Prims.string
  | OP_MIXFIX_ACCESS of Prims.string
  | OP_MIXFIX_ASSIGNMENT of Prims.string
  | PERCENT_LBRACK
  | PIPE_RIGHT
  | POLYMONADIC_BIND
  | POLYMONADIC_SUBCOMP
  | PRAGMA_POP_OPTIONS
  | PRAGMA_PRINT_EFFECTS_GRAPH
  | PRAGMA_PUSH_OPTIONS
  | PRAGMA_RESET_OPTIONS
  | PRAGMA_RESTART_SOLVER
  | PRAGMA_SET_OPTIONS
  | PRIVATE
  | QMARK
  | QMARK_DOT
  | QUOTE
  | RANGE of Prims.string
  | RANGE_OF
  | RARROW
  | RBRACE
  | RBRACK
  | REAL of Prims.string
  | REC
  | REFLECTABLE
  | REIFIABLE
  | REIFY
  | REQUIRES
  | RETURNS
  | RETURNS_EQ
  | RPAREN
  | SEMICOLON
  | SEMICOLON_OP of Prims.string option
  | SET_RANGE_OF
  | SIZET of Prims.string
  | SPLICE
  | SQUIGGLY_RARROW
  | STRING of Prims.string
  | SUBKIND
  | SUBTYPE
  | SUB_EFFECT
  | SYNTH
  | THEN
  | TILDE of Prims.string
  | TOTAL
  | TRUE
  | TRY
  | TVAR of Prims.string
  | TYPE
  | TYP_APP_GREATER
  | TYP_APP_LESS
  | UINT16 of Prims.string
  | UINT32 of Prims.string
  | UINT64 of Prims.string
  | UINT8 of Prims.string
  | UNDERSCORE
  | UNFOLD
  | UNFOLDABLE
  | UNIV_HASH
  | UNOPTEQUALITY
  | VAL
  | WHEN
  | WITH
val logic_qualifier_deprecation_warning : string
val mk_meta_tac : FStar_Parser_AST.term -> FStar_Parser_AST.arg_qualifier
val old_attribute_syntax_warning : string
val do_notation_deprecation_warning : string
val none_to_empty_list : 'a list option -> 'a list
val yytransl_const : int array
val yytransl_block : int array
val yylhs : string
val yylen : string
val yydefred : string
val yydgoto : string
val yysindex : string
val yyrindex : string
val yygindex : string
val yytablesize : int
val yytable : string
val yycheck : string
val yynames_const : string
val yynames_block : string
val yyact : (Parsing.parser_env -> Obj.t) array
val yytables : Parsing.parse_tables
val inputFragment :
  (Lexing.lexbuf -> token) -> Lexing.lexbuf -> FStar_Parser_AST.inputFragment
val oneDeclOrEOF :
  (Lexing.lexbuf -> token) -> Lexing.lexbuf -> FStar_Parser_AST.decl option
val term : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> FStar_Parser_AST.term
val warn_error_list :
  (Lexing.lexbuf -> token) ->
  Lexing.lexbuf -> (FStar_Errors_Codes.error_flag * Prims.string) Prims.list
