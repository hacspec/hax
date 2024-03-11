module Core.Ops.Index

class t_Index t_Self t_Idx = {
  f_Output: Type0;
  f_index_pre: s:t_Self -> i:t_Idx -> Type0;
  f_index_post: s:t_Self -> i:t_Idx -> f_Output -> Type0;
  f_index: s:t_Self -> i:t_Idx -> Pure f_Output (f_index_pre s i) (fun r -> f_index_post s i r);
}

