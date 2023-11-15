module Core.Ops.Index

class t_Index t_Self t_Idx = {
  f_Output: Type;
  in_range: t_Self -> t_Idx -> Type0;
  f_index: s:t_Self -> i:t_Idx{in_range s i} -> f_Output;
}

