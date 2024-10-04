module Std.Io

open Core
open FStar.Mul

class t_Read (v_Self: Type0) = {
  f_read_pre:v_Self -> t_Slice u8 -> bool;
  f_read_post:v_Self -> t_Slice u8 -> (v_Self & t_Slice u8 & Core.Result.t_Result usize Std.Io.Error.t_Error)
    -> bool;
  f_read:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure (v_Self & t_Slice u8 & Core.Result.t_Result usize Std.Io.Error.t_Error)
        (f_read_pre x0 x1)
        (fun result -> f_read_post x0 x1 result)
}

class t_Write (v_Self: Type0) = {
  f_write_pre:v_Self -> t_Slice u8 -> bool;
  f_write_post:v_Self -> t_Slice u8 -> (v_Self & Core.Result.t_Result usize Std.Io.Error.t_Error) -> bool;
  f_write:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure (v_Self & Core.Result.t_Result usize Std.Io.Error.t_Error)
        (f_write_pre x0 x1)
        (fun result -> f_write_post x0 x1 result);
  f_flush_pre:v_Self -> bool;
  f_flush_post:v_Self -> (v_Self & Core.Result.t_Result Prims.unit Std.Io.Error.t_Error) -> bool;
  f_flush:x0: v_Self
    -> Prims.Pure (v_Self & Core.Result.t_Result Prims.unit Std.Io.Error.t_Error)
        (f_flush_pre x0)
        (fun result -> f_flush_post x0 result)
}
