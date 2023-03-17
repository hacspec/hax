require import AllCore.
require import Hacspec.

clone import Hacspec.WordArray as State with
  theory Word <- WU32,
  op size <= 16.

clone import Hacspec.WordArray as Constants with
  theory Word <- WU32,
  op size <= 4.

clone import Hacspec.Bytes as Block with
  op size <= 64.

clone import Hacspec.Bytes as ChaChaIV with
  op size <= 12.

clone import Hacspec.Bytes as ChaChaKey with
  op size <= 32.

theory Hacspec_chacha20.
module Procs = {
  proc chacha20_line(a : int, b : int, d : int, s : int, m : State.t) = {
    var state : State.t;

    state <- m;
    state.[a] <- ((state).[a]) + ((state).[b]);
    state.[d] <- ((state).[d]) ^ ((state).[a]);
    state.[d] <- rotate_left ((state).[d]) (s);
    return state;
  }
  
  proc chacha20_quarter_round(a : int, b : int, c : int, d : int, state : State.t) = {
    var aout : State.t;

    state <@ chacha20_line ((a), (b), (d), (16), (state));
    state <@ chacha20_line ((c), (d), (b), (12), (state));
    state <@ chacha20_line ((a), (b), (d), (8), (state));
    aout <@ chacha20_line ((c), (d), (b), (7), (state));
    return aout;
  }
  
  proc chacha20_double_round(state : State.t) = {
    var aout : State.t;

    state <@ chacha20_quarter_round ((0), (4), (8), (12), (state));
    state <@ chacha20_quarter_round ((1), (5), (9), (13), (state));
    state <@ chacha20_quarter_round ((2), (6), (10), (14), (state));
    state <@ chacha20_quarter_round ((3), (7), (11), (15), (state));
    state <@ chacha20_quarter_round ((0), (5), (10), (15), (state));
    state <@ chacha20_quarter_round ((1), (6), (11), (12), (state));
    state <@ chacha20_quarter_round ((2), (7), (8), (13), (state));
    aout <@ chacha20_quarter_round ((3), (4), (9), (14), (state));
    return aout;
  }

  proc chacha20_rounds(state : State.t) = {
    var st : State.t;
    var _i : int;

    st <- state;
    _i <- 0;
    while (_i < 10) {
      st <@ chacha20_double_round (st);
      _i <- _i + 1;
    }
    return st;
  }
  

  proc chacha20_core(ctr : WU32.t, st0 : State.t) = {
    var state : State.t;
    var k : State.t;

    state <- st0;
    state.[12] <- ((state).[12]) + (ctr);
    k <@ chacha20_rounds (state);
    return (k) + (state);
  }
  
  proc chacha20_constants_init() = {
    var constants : Constants.t;

    constants <- Constants.new;
    constants.[0] <- WU32.ofint 1634760805;
    constants.[1] <- WU32.ofint 857760878;
    constants.[2] <- WU32.ofint 2036477234;
    constants.[3] <- WU32.ofint 1797285236;
    return constants;
  }

  proc chacha20_init(key : ChaChaKey.t, iv : ChaChaIV.t, ctr : WU32.t) : State.t = {
    var st : State.t;
    var tmp1 : Constants.t;

    st <- State.new;
    tmp1 <@ chacha20_constants_init();
    st <- update_u8 (st) (0) (to_le_bytes tmp1);
    st <- update_u32 (st) (4) (ChaChaKey.to_le_U32s (key));
    st.[12] <- ctr;
    st <- update_u32 (st) (13) (ChaChaIV.to_le_U32s (iv));
    return st;
  }

  proc chacha20_key_block(state : State.t) = {
    state <@ chacha20_core ((WU32.ofint 0), (state));
    return Block.from_seq_u8 (State.to_le_bytes (state));
  }

  proc chacha20_key_block0(key : ChaChaKey.t, iv : ChaChaIV.t) = {
    var state : State.t;
    var aout : Block.t;

    state <@ chacha20_init ((key), (iv), (WU32.ofint 0));
    aout <@ chacha20_key_block (state);
    return aout;
  }

  proc chacha20_encrypt_block(st0 : State.t, ctr : WU32.t, plain : Block.t) = {
    var st : State.t;
    var pl : State.t;

    st <@ chacha20_core ((ctr), (st0));
    pl <- State.from_seq_u32 (Block.to_le_U32s (plain));
    st <- (pl) ^ (st);
    return Block.from_seq_u8 (State.to_le_bytes (st));
  }

  proc chacha20_encrypt_last(st0 : State.t, ctr : WU32.t, plain : ByteSeq.t) : ByteSeq.t = {
    var b : Block.t;

    b <- Block.new;
    b <- Block.update (b) (0) (plain);
    b <@ chacha20_encrypt_block ((st0), (ctr), (b));
    return Block.slice (b) (0) (size (plain));
  }
  
  proc chacha20_update(st0 : State.t, m : ByteSeq.t) = {
    var blocks_out : ByteSeq.t;
    var n_blocks : int;
    var i : int;
    var msg_block : ByteSeq.t;
    var b : Block.t;
    var last_block : ByteSeq.t;
    var b' : ByteSeq.t;

    blocks_out <- ByteSeq.new (ByteSeq.len m);
    n_blocks <- ByteSeq.num_exact_chunks (m) (64);
    i <- 0;
    while (i < n_blocks) {
      msg_block <- ByteSeq.get_exact_chunk (m) (64) (i);
      b <@ chacha20_encrypt_block ((st0), WU32.ofint i, (Block.from_seq_u8 (msg_block)));
      blocks_out <- ByteSeq.set_exact_chunk (blocks_out) (64) (i) (Block.to_seq_u8 (b));
      i <- i + 1;      
    }
    last_block <- ByteSeq.get_remainder_chunk (m) (64);
    if ((ByteSeq.len (last_block)) <> (0)) {
      b' <@ chacha20_encrypt_last ((st0), (WU32.ofint n_blocks), (last_block));
      blocks_out <- ByteSeq.set_chunk (blocks_out) (64) (n_blocks) (b');
    }
    return blocks_out;
  }

  proc chacha20(key : ChaChaKey.t, iv : ChaChaIV.t, ctr : WU32.t, m : ByteSeq.t) = {
    var state : State.t;
    var aout : ByteSeq.t;

    state <@ chacha20_init ((key), (iv), (ctr));
    aout <@ chacha20_update ((state), (m));
    return aout;
  }
}.
end Hacspec_chacha20.
