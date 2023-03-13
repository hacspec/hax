use hacspec_lib::*;

// Jasmin
fn xor(x_inp : u64, y_inp : u64) -> u64 {
    let mut x : u64 = x_inp;
    let mut y : u64 = y_inp;
    let mut r : u64 = x ^ y;
    r
}
