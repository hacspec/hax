//! @fls: fls_1ji7368ieg0b, fls_3bucpdj828bq, fls_3etom5uu8y4u, fls_3of516eo0kkx, fls_490a1b74fut6, fls_66m2hwkju0vv, fls_6fq6bvxxvhsr, fls_6tb74n6lu0wf, fls_6z45ss502alt, fls_7mjv1xd45qr4, fls_8nyu6phm1nji, fls_8wux08bmpse, fls_axwrv7b3zt55, fls_b1vfpvsdv38, fls_b5fraqx07wuo, fls_br4g7qwfczig, fls_dyo3o1h3keqr, fls_e0a1e8ddph7, fls_fc62yaqyjpl2, fls_fobs8ebt7dhc, fls_fsn32kmwg65u, fls_g7hoyfqy9mu1, fls_ib8p7dfwddx2, fls_idxf02p7jogu, fls_j6kffhbxdm7o, fls_kjhma680hz3g, fls_krtbrpwf3mh0, fls_kwg8a351vc7, fls_ljc6jq5ksbcs, fls_pbpzkfo1fgtz, fls_qls0wj8bmupz, fls_qvofy4wkql0s, fls_rpapnm3afan8, fls_tg0kya5125jt, fls_to4e7imq2c0w, fls_ucFupTeCyylb, fls_v1bnk7neb82a, fls_w4lpq9bs8tsc, fls_wqs0792nud4e, fls_xguga84v3j8u, fls_y1ezabo61nyk, fls_y6ore0iwx7e0, fls_yiks5bvojncc, fls_zcuzhw7qkzkr, fls_zyuxqty09SDO
//! @title: Constant expressions built from literals, operators, blocks, calls, and control flow
//! @lean(tier): supported

pub struct Pair(pub u32, pub u32);

pub const fn double(x: u32) -> u32 {
    x * 2
}

pub const BASE: u32 = 3;
pub const SUM: u32 = BASE + double(2);
pub const ARRAY: [u32; 3] = [SUM, SUM - 1, SUM & 1];
pub const TUPLE: (u32, bool) = (ARRAY[0], ARRAY[0] > 5 && !false);
pub const PAIR: Pair = Pair(TUPLE.0, if TUPLE.1 { 1 } else { 0 });
pub const CHOSEN: u32 = match PAIR.1 {
    1 => { let x = -(PAIR.0 as i32); (x * -1) as u32 }
    _ => 0,
};
pub const REPEATED: [u8; (SUM as usize) - 5] = [1; (SUM as usize) - 5];
pub const BORROWED: &u32 = &CHOSEN;
pub const LOOPED: u32 = {
    let mut i = 0;
    let mut acc = 0;
    while i < 3 {
        acc += i;
        i += 1;
    }
    acc
};

#[hax_test::equiv]
pub fn constants_evaluate() -> bool {
    SUM == 7 && ARRAY == [7, 6, 1] && TUPLE == (7, true) && PAIR.1 == 1 && CHOSEN == 7 && REPEATED.len() == 2 && *BORROWED == 7 && LOOPED == 3
}
