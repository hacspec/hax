//! @fls: fls_1cyo5qhbl1j9, fls_4t6imtiw6kzt, fls_7p6zrjbpj0kl, fls_7ql1c71eidg8, fls_9bbewx1l7h5h, fls_9lt4wh9ql5ae, fls_QpBu34U6hXn9, fls_RZjFs9koNOk8, fls_bu6i3mcvnbin, fls_cu2ubdm3tfwb, fls_fvgfx17ossd9, fls_ggr5i91vur0r, fls_hwalzgdidbfz, fls_ixebnlcccmit, fls_jvz5z3eqxb39, fls_nb0eqky2akzt, fls_p52mfvpadu7w, fls_s3q3sej1hgho, fls_yrr1s0tucgvh
//! @title: Call expressions invoking functions and constructing tuple structs and variants
//! @lean(tier): supported

pub struct Meters(pub u32);

pub enum Msg {
    Move(i32, i32),
}

pub fn add(a: u32, b: u32) -> u32 {
    a + b
}

pub fn next(counter: &mut u32) -> u32 {
    *counter += 1;
    *counter
}

pub fn ordered_arguments() -> u32 {
    let mut c = 0;
    add(next(&mut c) * 10, next(&mut c))
}

#[hax_test::equiv]
pub fn calls_and_constructions() -> bool {
    let m = Meters(5);
    let dx = match Msg::Move(3, 4) {
        Msg::Move(x, _) => x,
    };
    add(1, 2) == 3 && ordered_arguments() == 12 && m.0 == 5 && dx == 3
}
