type level = Un | Expr | Type_level | Kind | Formula
val uu___is_Un : level -> Prims.bool
val uu___is_Expr : level -> Prims.bool
val uu___is_Type_level : level -> Prims.bool
val uu___is_Kind : level -> Prims.bool
val uu___is_Formula : level -> Prims.bool
type let_qualifier = NoLetQualifier | Rec
val uu___is_NoLetQualifier : let_qualifier -> Prims.bool
val uu___is_Rec : let_qualifier -> Prims.bool
type quote_kind = Static | Dynamic
val uu___is_Static : quote_kind -> Prims.bool
val uu___is_Dynamic : quote_kind -> Prims.bool
type term' =
    Wild
  | Const of FStar_Const.sconst
  | Op of (FStar_Ident.ident * term Prims.list)
  | Tvar of FStar_Ident.ident
  | Uvar of FStar_Ident.ident
  | Var of FStar_Ident.lid
  | Name of FStar_Ident.lid
  | Projector of (FStar_Ident.lid * FStar_Ident.ident)
  | Construct of (FStar_Ident.lid * (term * imp) Prims.list)
  | Abs of (pattern Prims.list * term)
  | App of (term * term * imp)
  | Let of
      (let_qualifier *
       (term Prims.list FStar_Pervasives_Native.option * (pattern * term))
       Prims.list * term)
  | LetOperator of ((FStar_Ident.ident * pattern * term) Prims.list * term)
  | LetOpen of (FStar_Ident.lid * term)
  | LetOpenRecord of (term * term * term)
  | Seq of (term * term)
  | Bind of (FStar_Ident.ident * term * term)
  | If of
      (term * FStar_Ident.ident FStar_Pervasives_Native.option *
       (FStar_Ident.ident FStar_Pervasives_Native.option * term * Prims.bool)
       FStar_Pervasives_Native.option * term * term)
  | Match of
      (term * FStar_Ident.ident FStar_Pervasives_Native.option *
       (FStar_Ident.ident FStar_Pervasives_Native.option * term * Prims.bool)
       FStar_Pervasives_Native.option *
       (pattern * term FStar_Pervasives_Native.option * term) Prims.list)
  | TryWith of
      (term *
       (pattern * term FStar_Pervasives_Native.option * term) Prims.list)
  | Ascribed of
      (term * term * term FStar_Pervasives_Native.option * Prims.bool)
  | Record of
      (term FStar_Pervasives_Native.option *
       (FStar_Ident.lid * term) Prims.list)
  | Project of (term * FStar_Ident.lid)
  | Product of (binder Prims.list * term)
  | Sum of ((binder, term) FStar_Pervasives.either Prims.list * term)
  | QForall of
      (binder Prims.list *
       (FStar_Ident.ident Prims.list * term Prims.list Prims.list) * 
       term)
  | QExists of
      (binder Prims.list *
       (FStar_Ident.ident Prims.list * term Prims.list Prims.list) * 
       term)
  | Refine of (binder * term)
  | NamedTyp of (FStar_Ident.ident * term)
  | Paren of term
  | Requires of (term * Prims.string FStar_Pervasives_Native.option)
  | Ensures of (term * Prims.string FStar_Pervasives_Native.option)
  | LexList of term Prims.list
  | WFOrder of (term * term)
  | Decreases of (term * Prims.string FStar_Pervasives_Native.option)
  | Labeled of (term * Prims.string * Prims.bool)
  | Discrim of FStar_Ident.lid
  | Attributes of term Prims.list
  | Antiquote of term
  | Quote of (term * quote_kind)
  | VQuote of term
  | CalcProof of (term * term * calc_step Prims.list)
  | IntroForall of (binder Prims.list * term * term)
  | IntroExists of (binder Prims.list * term * term Prims.list * term)
  | IntroImplies of (term * term * binder * term)
  | IntroOr of (Prims.bool * term * term * term)
  | IntroAnd of (term * term * term * term)
  | ElimForall of (binder Prims.list * term * term Prims.list)
  | ElimExists of (binder Prims.list * term * term * binder * term)
  | ElimImplies of (term * term * term)
  | ElimOr of (term * term * term * binder * term * binder * term)
  | ElimAnd of (term * term * term * binder * binder * term)
and term = { tm : term'; range : FStar_Compiler_Range.range; level : level; }
and calc_step = CalcStep of (term * term * term)
and binder' =
    Variable of FStar_Ident.ident
  | TVariable of FStar_Ident.ident
  | Annotated of (FStar_Ident.ident * term)
  | TAnnotated of (FStar_Ident.ident * term)
  | NoName of term
and binder = {
  b : binder';
  brange : FStar_Compiler_Range.range;
  blevel : level;
  aqual : arg_qualifier FStar_Pervasives_Native.option;
  battributes : term Prims.list;
}
and pattern' =
    PatWild of
      (arg_qualifier FStar_Pervasives_Native.option * term Prims.list)
  | PatConst of FStar_Const.sconst
  | PatApp of (pattern * pattern Prims.list)
  | PatVar of
      (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option *
       term Prims.list)
  | PatName of FStar_Ident.lid
  | PatTvar of
      (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option *
       term Prims.list)
  | PatList of pattern Prims.list
  | PatTuple of (pattern Prims.list * Prims.bool)
  | PatRecord of (FStar_Ident.lid * pattern) Prims.list
  | PatAscribed of (pattern * (term * term FStar_Pervasives_Native.option))
  | PatOr of pattern Prims.list
  | PatOp of FStar_Ident.ident
  | PatVQuote of term
and pattern = { pat : pattern'; prange : FStar_Compiler_Range.range; }
and arg_qualifier = Implicit | Equality | Meta of term | TypeClassArg
and imp = FsTypApp | Hash | UnivApp | HashBrace of term | Infix | Nothing
val uu___is_Wild : term' -> Prims.bool
val uu___is_Const : term' -> Prims.bool
val __proj__Const__item___0 : term' -> FStar_Const.sconst
val uu___is_Op : term' -> Prims.bool
val __proj__Op__item___0 : term' -> FStar_Ident.ident * term Prims.list
val uu___is_Tvar : term' -> Prims.bool
val __proj__Tvar__item___0 : term' -> FStar_Ident.ident
val uu___is_Uvar : term' -> Prims.bool
val __proj__Uvar__item___0 : term' -> FStar_Ident.ident
val uu___is_Var : term' -> Prims.bool
val __proj__Var__item___0 : term' -> FStar_Ident.lid
val uu___is_Name : term' -> Prims.bool
val __proj__Name__item___0 : term' -> FStar_Ident.lid
val uu___is_Projector : term' -> Prims.bool
val __proj__Projector__item___0 :
  term' -> FStar_Ident.lid * FStar_Ident.ident
val uu___is_Construct : term' -> Prims.bool
val __proj__Construct__item___0 :
  term' -> FStar_Ident.lid * (term * imp) Prims.list
val uu___is_Abs : term' -> Prims.bool
val __proj__Abs__item___0 : term' -> pattern Prims.list * term
val uu___is_App : term' -> Prims.bool
val __proj__App__item___0 : term' -> term * term * imp
val uu___is_Let : term' -> Prims.bool
val __proj__Let__item___0 :
  term' ->
  let_qualifier *
  (term Prims.list FStar_Pervasives_Native.option * (pattern * term))
  Prims.list * term
val uu___is_LetOperator : term' -> Prims.bool
val __proj__LetOperator__item___0 :
  term' -> (FStar_Ident.ident * pattern * term) Prims.list * term
val uu___is_LetOpen : term' -> Prims.bool
val __proj__LetOpen__item___0 : term' -> FStar_Ident.lid * term
val uu___is_LetOpenRecord : term' -> Prims.bool
val __proj__LetOpenRecord__item___0 : term' -> term * term * term
val uu___is_Seq : term' -> Prims.bool
val __proj__Seq__item___0 : term' -> term * term
val uu___is_Bind : term' -> Prims.bool
val __proj__Bind__item___0 : term' -> FStar_Ident.ident * term * term
val uu___is_If : term' -> Prims.bool
val __proj__If__item___0 :
  term' ->
  term * FStar_Ident.ident FStar_Pervasives_Native.option *
  (FStar_Ident.ident FStar_Pervasives_Native.option * term * Prims.bool)
  FStar_Pervasives_Native.option * term * term
val uu___is_Match : term' -> Prims.bool
val __proj__Match__item___0 :
  term' ->
  term * FStar_Ident.ident FStar_Pervasives_Native.option *
  (FStar_Ident.ident FStar_Pervasives_Native.option * term * Prims.bool)
  FStar_Pervasives_Native.option *
  (pattern * term FStar_Pervasives_Native.option * term) Prims.list
val uu___is_TryWith : term' -> Prims.bool
val __proj__TryWith__item___0 :
  term' ->
  term * (pattern * term FStar_Pervasives_Native.option * term) Prims.list
val uu___is_Ascribed : term' -> Prims.bool
val __proj__Ascribed__item___0 :
  term' -> term * term * term FStar_Pervasives_Native.option * Prims.bool
val uu___is_Record : term' -> Prims.bool
val __proj__Record__item___0 :
  term' ->
  term FStar_Pervasives_Native.option * (FStar_Ident.lid * term) Prims.list
val uu___is_Project : term' -> Prims.bool
val __proj__Project__item___0 : term' -> term * FStar_Ident.lid
val uu___is_Product : term' -> Prims.bool
val __proj__Product__item___0 : term' -> binder Prims.list * term
val uu___is_Sum : term' -> Prims.bool
val __proj__Sum__item___0 :
  term' -> (binder, term) FStar_Pervasives.either Prims.list * term
val uu___is_QForall : term' -> Prims.bool
val __proj__QForall__item___0 :
  term' ->
  binder Prims.list *
  (FStar_Ident.ident Prims.list * term Prims.list Prims.list) * term
val uu___is_QExists : term' -> Prims.bool
val __proj__QExists__item___0 :
  term' ->
  binder Prims.list *
  (FStar_Ident.ident Prims.list * term Prims.list Prims.list) * term
val uu___is_Refine : term' -> Prims.bool
val __proj__Refine__item___0 : term' -> binder * term
val uu___is_NamedTyp : term' -> Prims.bool
val __proj__NamedTyp__item___0 : term' -> FStar_Ident.ident * term
val uu___is_Paren : term' -> Prims.bool
val __proj__Paren__item___0 : term' -> term
val uu___is_Requires : term' -> Prims.bool
val __proj__Requires__item___0 :
  term' -> term * Prims.string FStar_Pervasives_Native.option
val uu___is_Ensures : term' -> Prims.bool
val __proj__Ensures__item___0 :
  term' -> term * Prims.string FStar_Pervasives_Native.option
val uu___is_LexList : term' -> Prims.bool
val __proj__LexList__item___0 : term' -> term Prims.list
val uu___is_WFOrder : term' -> Prims.bool
val __proj__WFOrder__item___0 : term' -> term * term
val uu___is_Decreases : term' -> Prims.bool
val __proj__Decreases__item___0 :
  term' -> term * Prims.string FStar_Pervasives_Native.option
val uu___is_Labeled : term' -> Prims.bool
val __proj__Labeled__item___0 : term' -> term * Prims.string * Prims.bool
val uu___is_Discrim : term' -> Prims.bool
val __proj__Discrim__item___0 : term' -> FStar_Ident.lid
val uu___is_Attributes : term' -> Prims.bool
val __proj__Attributes__item___0 : term' -> term Prims.list
val uu___is_Antiquote : term' -> Prims.bool
val __proj__Antiquote__item___0 : term' -> term
val uu___is_Quote : term' -> Prims.bool
val __proj__Quote__item___0 : term' -> term * quote_kind
val uu___is_VQuote : term' -> Prims.bool
val __proj__VQuote__item___0 : term' -> term
val uu___is_CalcProof : term' -> Prims.bool
val __proj__CalcProof__item___0 : term' -> term * term * calc_step Prims.list
val uu___is_IntroForall : term' -> Prims.bool
val __proj__IntroForall__item___0 : term' -> binder Prims.list * term * term
val uu___is_IntroExists : term' -> Prims.bool
val __proj__IntroExists__item___0 :
  term' -> binder Prims.list * term * term Prims.list * term
val uu___is_IntroImplies : term' -> Prims.bool
val __proj__IntroImplies__item___0 : term' -> term * term * binder * term
val uu___is_IntroOr : term' -> Prims.bool
val __proj__IntroOr__item___0 : term' -> Prims.bool * term * term * term
val uu___is_IntroAnd : term' -> Prims.bool
val __proj__IntroAnd__item___0 : term' -> term * term * term * term
val uu___is_ElimForall : term' -> Prims.bool
val __proj__ElimForall__item___0 :
  term' -> binder Prims.list * term * term Prims.list
val uu___is_ElimExists : term' -> Prims.bool
val __proj__ElimExists__item___0 :
  term' -> binder Prims.list * term * term * binder * term
val uu___is_ElimImplies : term' -> Prims.bool
val __proj__ElimImplies__item___0 : term' -> term * term * term
val uu___is_ElimOr : term' -> Prims.bool
val __proj__ElimOr__item___0 :
  term' -> term * term * term * binder * term * binder * term
val uu___is_ElimAnd : term' -> Prims.bool
val __proj__ElimAnd__item___0 :
  term' -> term * term * term * binder * binder * term
val __proj__Mkterm__item__tm : term -> term'
val __proj__Mkterm__item__range : term -> FStar_Compiler_Range.range
val __proj__Mkterm__item__level : term -> level
val uu___is_CalcStep : calc_step -> Prims.bool
val __proj__CalcStep__item___0 : calc_step -> term * term * term
val uu___is_Variable : binder' -> Prims.bool
val __proj__Variable__item___0 : binder' -> FStar_Ident.ident
val uu___is_TVariable : binder' -> Prims.bool
val __proj__TVariable__item___0 : binder' -> FStar_Ident.ident
val uu___is_Annotated : binder' -> Prims.bool
val __proj__Annotated__item___0 : binder' -> FStar_Ident.ident * term
val uu___is_TAnnotated : binder' -> Prims.bool
val __proj__TAnnotated__item___0 : binder' -> FStar_Ident.ident * term
val uu___is_NoName : binder' -> Prims.bool
val __proj__NoName__item___0 : binder' -> term
val __proj__Mkbinder__item__b : binder -> binder'
val __proj__Mkbinder__item__brange : binder -> FStar_Compiler_Range.range
val __proj__Mkbinder__item__blevel : binder -> level
val __proj__Mkbinder__item__aqual :
  binder -> arg_qualifier FStar_Pervasives_Native.option
val __proj__Mkbinder__item__battributes : binder -> term Prims.list
val uu___is_PatWild : pattern' -> Prims.bool
val __proj__PatWild__item___0 :
  pattern' -> arg_qualifier FStar_Pervasives_Native.option * term Prims.list
val uu___is_PatConst : pattern' -> Prims.bool
val __proj__PatConst__item___0 : pattern' -> FStar_Const.sconst
val uu___is_PatApp : pattern' -> Prims.bool
val __proj__PatApp__item___0 : pattern' -> pattern * pattern Prims.list
val uu___is_PatVar : pattern' -> Prims.bool
val __proj__PatVar__item___0 :
  pattern' ->
  FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option *
  term Prims.list
val uu___is_PatName : pattern' -> Prims.bool
val __proj__PatName__item___0 : pattern' -> FStar_Ident.lid
val uu___is_PatTvar : pattern' -> Prims.bool
val __proj__PatTvar__item___0 :
  pattern' ->
  FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option *
  term Prims.list
val uu___is_PatList : pattern' -> Prims.bool
val __proj__PatList__item___0 : pattern' -> pattern Prims.list
val uu___is_PatTuple : pattern' -> Prims.bool
val __proj__PatTuple__item___0 : pattern' -> pattern Prims.list * Prims.bool
val uu___is_PatRecord : pattern' -> Prims.bool
val __proj__PatRecord__item___0 :
  pattern' -> (FStar_Ident.lid * pattern) Prims.list
val uu___is_PatAscribed : pattern' -> Prims.bool
val __proj__PatAscribed__item___0 :
  pattern' -> pattern * (term * term FStar_Pervasives_Native.option)
val uu___is_PatOr : pattern' -> Prims.bool
val __proj__PatOr__item___0 : pattern' -> pattern Prims.list
val uu___is_PatOp : pattern' -> Prims.bool
val __proj__PatOp__item___0 : pattern' -> FStar_Ident.ident
val uu___is_PatVQuote : pattern' -> Prims.bool
val __proj__PatVQuote__item___0 : pattern' -> term
val __proj__Mkpattern__item__pat : pattern -> pattern'
val __proj__Mkpattern__item__prange : pattern -> FStar_Compiler_Range.range
val uu___is_Implicit : arg_qualifier -> Prims.bool
val uu___is_Equality : arg_qualifier -> Prims.bool
val uu___is_Meta : arg_qualifier -> Prims.bool
val __proj__Meta__item___0 : arg_qualifier -> term
val uu___is_TypeClassArg : arg_qualifier -> Prims.bool
val uu___is_FsTypApp : imp -> Prims.bool
val uu___is_Hash : imp -> Prims.bool
val uu___is_UnivApp : imp -> Prims.bool
val uu___is_HashBrace : imp -> Prims.bool
val __proj__HashBrace__item___0 : imp -> term
val uu___is_Infix : imp -> Prims.bool
val uu___is_Nothing : imp -> Prims.bool
type match_returns_annotation =
    FStar_Ident.ident FStar_Pervasives_Native.option * term * Prims.bool
type patterns = FStar_Ident.ident Prims.list * term Prims.list Prims.list
type attributes_ = term Prims.list
type branch = pattern * term FStar_Pervasives_Native.option * term
type aqual = arg_qualifier FStar_Pervasives_Native.option
type knd = term
type typ = term
type expr = term
type tycon_record =
    (FStar_Ident.ident * aqual * attributes_ * term) Prims.list
type constructor_payload =
    VpOfNotation of typ
  | VpArbitrary of typ
  | VpRecord of (tycon_record * typ FStar_Pervasives_Native.option)
val uu___is_VpOfNotation : constructor_payload -> Prims.bool
val __proj__VpOfNotation__item___0 : constructor_payload -> typ
val uu___is_VpArbitrary : constructor_payload -> Prims.bool
val __proj__VpArbitrary__item___0 : constructor_payload -> typ
val uu___is_VpRecord : constructor_payload -> Prims.bool
val __proj__VpRecord__item___0 :
  constructor_payload -> tycon_record * typ FStar_Pervasives_Native.option
type tycon =
    TyconAbstract of
      (FStar_Ident.ident * binder Prims.list *
       knd FStar_Pervasives_Native.option)
  | TyconAbbrev of
      (FStar_Ident.ident * binder Prims.list *
       knd FStar_Pervasives_Native.option * term)
  | TyconRecord of
      (FStar_Ident.ident * binder Prims.list *
       knd FStar_Pervasives_Native.option * attributes_ * tycon_record)
  | TyconVariant of
      (FStar_Ident.ident * binder Prims.list *
       knd FStar_Pervasives_Native.option *
       (FStar_Ident.ident *
        constructor_payload FStar_Pervasives_Native.option * attributes_)
       Prims.list)
val uu___is_TyconAbstract : tycon -> Prims.bool
val __proj__TyconAbstract__item___0 :
  tycon ->
  FStar_Ident.ident * binder Prims.list * knd FStar_Pervasives_Native.option
val uu___is_TyconAbbrev : tycon -> Prims.bool
val __proj__TyconAbbrev__item___0 :
  tycon ->
  FStar_Ident.ident * binder Prims.list *
  knd FStar_Pervasives_Native.option * term
val uu___is_TyconRecord : tycon -> Prims.bool
val __proj__TyconRecord__item___0 :
  tycon ->
  FStar_Ident.ident * binder Prims.list *
  knd FStar_Pervasives_Native.option * attributes_ * tycon_record
val uu___is_TyconVariant : tycon -> Prims.bool
val __proj__TyconVariant__item___0 :
  tycon ->
  FStar_Ident.ident * binder Prims.list *
  knd FStar_Pervasives_Native.option *
  (FStar_Ident.ident * constructor_payload FStar_Pervasives_Native.option *
   attributes_)
  Prims.list
type qualifier =
    Private
  | Noeq
  | Unopteq
  | Assumption
  | DefaultEffect
  | TotalEffect
  | Effect_qual
  | New
  | Inline
  | Visible
  | Unfold_for_unification_and_vcgen
  | Inline_for_extraction
  | Irreducible
  | NoExtract
  | Reifiable
  | Reflectable
  | Opaque
  | Logic
val uu___is_Private : qualifier -> Prims.bool
val uu___is_Noeq : qualifier -> Prims.bool
val uu___is_Unopteq : qualifier -> Prims.bool
val uu___is_Assumption : qualifier -> Prims.bool
val uu___is_DefaultEffect : qualifier -> Prims.bool
val uu___is_TotalEffect : qualifier -> Prims.bool
val uu___is_Effect_qual : qualifier -> Prims.bool
val uu___is_New : qualifier -> Prims.bool
val uu___is_Inline : qualifier -> Prims.bool
val uu___is_Visible : qualifier -> Prims.bool
val uu___is_Unfold_for_unification_and_vcgen : qualifier -> Prims.bool
val uu___is_Inline_for_extraction : qualifier -> Prims.bool
val uu___is_Irreducible : qualifier -> Prims.bool
val uu___is_NoExtract : qualifier -> Prims.bool
val uu___is_Reifiable : qualifier -> Prims.bool
val uu___is_Reflectable : qualifier -> Prims.bool
val uu___is_Opaque : qualifier -> Prims.bool
val uu___is_Logic : qualifier -> Prims.bool
type qualifiers = qualifier Prims.list
type decoration = Qualifier of qualifier | DeclAttributes of term Prims.list
val uu___is_Qualifier : decoration -> Prims.bool
val __proj__Qualifier__item___0 : decoration -> qualifier
val uu___is_DeclAttributes : decoration -> Prims.bool
val __proj__DeclAttributes__item___0 : decoration -> term Prims.list
type lift_op =
    NonReifiableLift of term
  | ReifiableLift of (term * term)
  | LiftForFree of term
val uu___is_NonReifiableLift : lift_op -> Prims.bool
val __proj__NonReifiableLift__item___0 : lift_op -> term
val uu___is_ReifiableLift : lift_op -> Prims.bool
val __proj__ReifiableLift__item___0 : lift_op -> term * term
val uu___is_LiftForFree : lift_op -> Prims.bool
val __proj__LiftForFree__item___0 : lift_op -> term
type lift = {
  msource : FStar_Ident.lid;
  mdest : FStar_Ident.lid;
  lift_op : lift_op;
  braced : Prims.bool;
}
val __proj__Mklift__item__msource : lift -> FStar_Ident.lid
val __proj__Mklift__item__mdest : lift -> FStar_Ident.lid
val __proj__Mklift__item__lift_op : lift -> lift_op
val __proj__Mklift__item__braced : lift -> Prims.bool
type pragma =
    SetOptions of Prims.string
  | ResetOptions of Prims.string FStar_Pervasives_Native.option
  | PushOptions of Prims.string FStar_Pervasives_Native.option
  | PopOptions
  | RestartSolver
  | PrintEffectsGraph
val uu___is_SetOptions : pragma -> Prims.bool
val __proj__SetOptions__item___0 : pragma -> Prims.string
val uu___is_ResetOptions : pragma -> Prims.bool
val __proj__ResetOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option
val uu___is_PushOptions : pragma -> Prims.bool
val __proj__PushOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option
val uu___is_PopOptions : pragma -> Prims.bool
val uu___is_RestartSolver : pragma -> Prims.bool
val uu___is_PrintEffectsGraph : pragma -> Prims.bool
type decl' =
    TopLevelModule of FStar_Ident.lid
  | Open of FStar_Ident.lid
  | Friend of FStar_Ident.lid
  | Include of FStar_Ident.lid
  | ModuleAbbrev of (FStar_Ident.ident * FStar_Ident.lid)
  | TopLevelLet of (let_qualifier * (pattern * term) Prims.list)
  | Tycon of (Prims.bool * Prims.bool * tycon Prims.list)
  | Val of (FStar_Ident.ident * term)
  | Exception of (FStar_Ident.ident * term FStar_Pervasives_Native.option)
  | NewEffect of effect_decl
  | LayeredEffect of effect_decl
  | SubEffect of lift
  | Polymonadic_bind of
      (FStar_Ident.lid * FStar_Ident.lid * FStar_Ident.lid * term)
  | Polymonadic_subcomp of (FStar_Ident.lid * FStar_Ident.lid * term)
  | Pragma of pragma
  | Assume of (FStar_Ident.ident * term)
  | Splice of (FStar_Ident.ident Prims.list * term)
and decl = {
  d : decl';
  drange : FStar_Compiler_Range.range;
  quals : qualifiers;
  attrs : attributes_;
}
and effect_decl =
    DefineEffect of
      (FStar_Ident.ident * binder Prims.list * term * decl Prims.list)
  | RedefineEffect of (FStar_Ident.ident * binder Prims.list * term)
val uu___is_TopLevelModule : decl' -> Prims.bool
val __proj__TopLevelModule__item___0 : decl' -> FStar_Ident.lid
val uu___is_Open : decl' -> Prims.bool
val __proj__Open__item___0 : decl' -> FStar_Ident.lid
val uu___is_Friend : decl' -> Prims.bool
val __proj__Friend__item___0 : decl' -> FStar_Ident.lid
val uu___is_Include : decl' -> Prims.bool
val __proj__Include__item___0 : decl' -> FStar_Ident.lid
val uu___is_ModuleAbbrev : decl' -> Prims.bool
val __proj__ModuleAbbrev__item___0 :
  decl' -> FStar_Ident.ident * FStar_Ident.lid
val uu___is_TopLevelLet : decl' -> Prims.bool
val __proj__TopLevelLet__item___0 :
  decl' -> let_qualifier * (pattern * term) Prims.list
val uu___is_Tycon : decl' -> Prims.bool
val __proj__Tycon__item___0 :
  decl' -> Prims.bool * Prims.bool * tycon Prims.list
val uu___is_Val : decl' -> Prims.bool
val __proj__Val__item___0 : decl' -> FStar_Ident.ident * term
val uu___is_Exception : decl' -> Prims.bool
val __proj__Exception__item___0 :
  decl' -> FStar_Ident.ident * term FStar_Pervasives_Native.option
val uu___is_NewEffect : decl' -> Prims.bool
val __proj__NewEffect__item___0 : decl' -> effect_decl
val uu___is_LayeredEffect : decl' -> Prims.bool
val __proj__LayeredEffect__item___0 : decl' -> effect_decl
val uu___is_SubEffect : decl' -> Prims.bool
val __proj__SubEffect__item___0 : decl' -> lift
val uu___is_Polymonadic_bind : decl' -> Prims.bool
val __proj__Polymonadic_bind__item___0 :
  decl' -> FStar_Ident.lid * FStar_Ident.lid * FStar_Ident.lid * term
val uu___is_Polymonadic_subcomp : decl' -> Prims.bool
val __proj__Polymonadic_subcomp__item___0 :
  decl' -> FStar_Ident.lid * FStar_Ident.lid * term
val uu___is_Pragma : decl' -> Prims.bool
val __proj__Pragma__item___0 : decl' -> pragma
val uu___is_Assume : decl' -> Prims.bool
val __proj__Assume__item___0 : decl' -> FStar_Ident.ident * term
val uu___is_Splice : decl' -> Prims.bool
val __proj__Splice__item___0 : decl' -> FStar_Ident.ident Prims.list * term
val __proj__Mkdecl__item__d : decl -> decl'
val __proj__Mkdecl__item__drange : decl -> FStar_Compiler_Range.range
val __proj__Mkdecl__item__quals : decl -> qualifiers
val __proj__Mkdecl__item__attrs : decl -> attributes_
val uu___is_DefineEffect : effect_decl -> Prims.bool
val __proj__DefineEffect__item___0 :
  effect_decl ->
  FStar_Ident.ident * binder Prims.list * term * decl Prims.list
val uu___is_RedefineEffect : effect_decl -> Prims.bool
val __proj__RedefineEffect__item___0 :
  effect_decl -> FStar_Ident.ident * binder Prims.list * term
type modul =
    Module of (FStar_Ident.lid * decl Prims.list)
  | Interface of (FStar_Ident.lid * decl Prims.list * Prims.bool)
val uu___is_Module : modul -> Prims.bool
val __proj__Module__item___0 : modul -> FStar_Ident.lid * decl Prims.list
val uu___is_Interface : modul -> Prims.bool
val __proj__Interface__item___0 :
  modul -> FStar_Ident.lid * decl Prims.list * Prims.bool
type file = modul
type inputFragment = (file, decl Prims.list) FStar_Pervasives.either
val decl_drange : decl -> FStar_Compiler_Range.range
val check_id : FStar_Ident.ident -> Prims.unit
val at_most_one :
  Prims.string ->
  FStar_Compiler_Range.range ->
  'uuuuu Prims.list -> 'uuuuu FStar_Pervasives_Native.option
val mk_decl :
  decl' -> FStar_Compiler_Range.range -> decoration Prims.list -> decl
val mk_binder_with_attrs :
  binder' ->
  FStar_Compiler_Range.range ->
  level ->
  arg_qualifier FStar_Pervasives_Native.option -> term Prims.list -> binder
val mk_binder :
  binder' ->
  FStar_Compiler_Range.range ->
  level -> arg_qualifier FStar_Pervasives_Native.option -> binder
val mk_term : term' -> FStar_Compiler_Range.range -> level -> term
val mk_uminus :
  term ->
  FStar_Compiler_Range.range -> FStar_Compiler_Range.range -> level -> term
val mk_pattern : pattern' -> FStar_Compiler_Range.range -> pattern
val un_curry_abs : pattern Prims.list -> term -> term'
val mk_function :
  (pattern * term FStar_Pervasives_Native.option * term) Prims.list ->
  FStar_Compiler_Range.range -> FStar_Compiler_Range.range -> term
val un_function :
  pattern -> term -> (pattern * term) FStar_Pervasives_Native.option
val lid_with_range :
  FStar_Ident.lident -> FStar_Compiler_Range.range -> FStar_Ident.lident
val consPat : FStar_Compiler_Range.range -> pattern -> pattern -> pattern'
val consTerm : FStar_Compiler_Range.range -> term -> term -> term
val mkConsList : FStar_Compiler_Range.range -> term Prims.list -> term
val unit_const : FStar_Compiler_Range.range -> term
val ml_comp : term -> term
val tot_comp : term -> term
val mkApp :
  term -> (term * imp) Prims.list -> FStar_Compiler_Range.range -> term
val mkRefSet : FStar_Compiler_Range.range -> term Prims.list -> term
val mkExplicitApp :
  term -> term Prims.list -> FStar_Compiler_Range.range -> term
val mkAdmitMagic : FStar_Compiler_Range.range -> term
val mkWildAdmitMagic :
  FStar_Compiler_Range.range ->
  pattern * 'uuuuu FStar_Pervasives_Native.option * term
val focusBranches :
  (Prims.bool * (pattern * 'uuuuu FStar_Pervasives_Native.option * term))
  Prims.list ->
  FStar_Compiler_Range.range ->
  (pattern * 'uuuuu FStar_Pervasives_Native.option * term) Prims.list
val focusLetBindings :
  (Prims.bool * ('uuuuu * term)) Prims.list ->
  FStar_Compiler_Range.range -> ('uuuuu * term) Prims.list
val focusAttrLetBindings :
  ('uuuuu * (Prims.bool * ('uuuuu1 * term))) Prims.list ->
  FStar_Compiler_Range.range -> ('uuuuu * ('uuuuu1 * term)) Prims.list
val mkFsTypApp :
  term -> term Prims.list -> FStar_Compiler_Range.range -> term
val mkTuple : term Prims.list -> FStar_Compiler_Range.range -> term
val mkDTuple : term Prims.list -> FStar_Compiler_Range.range -> term
val mkRefinedBinder :
  FStar_Ident.ident ->
  term ->
  Prims.bool ->
  term FStar_Pervasives_Native.option ->
  FStar_Compiler_Range.range ->
  arg_qualifier FStar_Pervasives_Native.option -> term Prims.list -> binder
val mkRefinedPattern :
  pattern ->
  term ->
  Prims.bool ->
  term FStar_Pervasives_Native.option ->
  FStar_Compiler_Range.range -> FStar_Compiler_Range.range -> pattern
val extract_named_refinement :
  term ->
  (FStar_Ident.ident * term * term FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.option
val as_mlist :
  (FStar_Ident.lid * decl) * decl Prims.list -> decl Prims.list -> modul
val as_frag : decl Prims.list -> inputFragment
val strip_prefix :
  Prims.string -> Prims.string -> Prims.string FStar_Pervasives_Native.option
val compile_op : Prims.int -> Prims.string -> 'uuuuu -> Prims.string
val compile_op' : Prims.string -> 'uuuuu -> Prims.string
val string_to_op :
  Prims.string ->
  (Prims.string * Prims.int FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.option
val string_of_fsdoc :
  Prims.string * (Prims.string * Prims.string) Prims.list -> Prims.string
val string_of_let_qualifier : let_qualifier -> Prims.string
val to_string_l :
  Prims.string ->
  ('uuuuu -> Prims.string) -> 'uuuuu Prims.list -> Prims.string
val imp_to_string : imp -> Prims.string
val term_to_string : term -> Prims.string
val binders_to_string : Prims.string -> binder Prims.list -> Prims.string
val try_or_match_to_string :
  term ->
  term ->
  (pattern * term FStar_Pervasives_Native.option * term) Prims.list ->
  FStar_Ident.ident FStar_Pervasives_Native.option ->
  (FStar_Ident.ident FStar_Pervasives_Native.option * term * Prims.bool)
  FStar_Pervasives_Native.option -> Prims.string
val calc_step_to_string : calc_step -> Prims.string
val binder_to_string : binder -> Prims.string
val aqual_to_string :
  arg_qualifier FStar_Pervasives_Native.option -> Prims.string
val attr_list_to_string : term Prims.list -> Prims.string
val pat_to_string : pattern -> Prims.string
val attrs_opt_to_string :
  term Prims.list FStar_Pervasives_Native.option -> Prims.string
val head_id_of_pat : pattern -> FStar_Ident.lid Prims.list
val lids_of_let : (pattern * 'uuuuu) Prims.list -> FStar_Ident.lid Prims.list
val id_of_tycon : tycon -> Prims.string
val string_of_pragma : pragma -> Prims.string
val decl_to_string : decl -> Prims.string
val modul_to_string : modul -> Prims.string
val decl_is_val : FStar_Ident.ident -> decl -> Prims.bool
val thunk : term -> term
val ident_of_binder :
  FStar_Compiler_Range.range -> binder -> FStar_Ident.ident
val idents_of_binders :
  binder Prims.list ->
  FStar_Compiler_Range.range -> FStar_Ident.ident Prims.list
val decl_syntax_is_delimited : decl -> Prims.bool
