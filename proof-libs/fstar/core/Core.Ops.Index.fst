module Core.Ops.Index

include Core.Ops.Index.IndexMut

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

class t_Index t_Self t_Idx = {
  f_Output: Type;
  in_range: t_Self -> t_Idx -> Type0;
  f_index: s:t_Self -> i:t_Idx{in_range s i} -> HST.St f_Output;
}

