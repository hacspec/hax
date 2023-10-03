module Core.Ops.Index

class t_Index t_Self t_Idx = {
  f_Output: Type;
  f_index: t_Self -> t_Idx -> f_Output;
}
