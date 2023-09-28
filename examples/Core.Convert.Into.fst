module Core.Convert.Into

open Core.Types

class into_tc self t = {
  into: self -> t;
}

let mk (into: 's -> 't): into_tc 's 't = {into}

instance _: into_tc u8 u16 = mk (fun x -> UInt16.uint_to_t (UInt8.v x))
instance _: into_tc u8 u32 = mk (fun x -> UInt32.uint_to_t (UInt8.v x))
instance _: into_tc u8 u64 = mk (fun x -> UInt64.uint_to_t (UInt8.v x))

instance _: into_tc u16 u32 = mk (fun x -> UInt32.uint_to_t (UInt16.v x))
instance _: into_tc u16 u64 = mk (fun x -> UInt64.uint_to_t (UInt16.v x))


