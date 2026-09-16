//! @fls: fls_i5ko1t2wbgxe, fls_54d5uydc87td, fls_7frvr2nm2mcj
//! @title: Labeled break out of a nested loop
//! @lean(tier): supported
//! @lean(reason): Annex A.1 of the input-language reference lists labeled break as a transient gap.

pub fn first_pair_summing_to(target: i32) -> (i32, i32) {
    let mut found = (0, 0);
    'outer: for i in 0..10 {
        for j in 0..10 {
            if i + j == target {
                found = (i, j);
                break 'outer;
            }
        }
    }
    found
}

#[hax_test::equiv]
pub fn breaks_outer_loop() -> bool {
    first_pair_summing_to(5) == (0, 5)
}
