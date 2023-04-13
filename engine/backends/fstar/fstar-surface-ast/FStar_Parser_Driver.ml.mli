val is_cache_file : Prims.string -> Prims.bool
type fragment =
    Empty
  | Modul of FStar_Parser_AST.modul
  | Decls of FStar_Parser_AST.decl Prims.list
  | DeclsWithContent of
      (FStar_Parser_AST.decl * FStar_Parser_ParseIt.code_fragment) Prims.list
val uu___is_Empty : fragment -> Prims.bool
val uu___is_Modul : fragment -> Prims.bool
val __proj__Modul__item___0 : fragment -> FStar_Parser_AST.modul
val uu___is_Decls : fragment -> Prims.bool
val __proj__Decls__item___0 : fragment -> FStar_Parser_AST.decl Prims.list
val uu___is_DeclsWithContent : fragment -> Prims.bool
val __proj__DeclsWithContent__item___0 :
  fragment ->
  (FStar_Parser_AST.decl * FStar_Parser_ParseIt.code_fragment) Prims.list
val parse_fragment : FStar_Parser_ParseIt.input_frag -> fragment
val parse_file :
  Prims.string ->
  FStar_Parser_AST.file *
  (Prims.string * FStar_Compiler_Range.range) Prims.list
