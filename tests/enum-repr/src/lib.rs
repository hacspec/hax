#![allow(dead_code)]

#[repr(u16)]
enum EnumWithRepr {
    ExplicitDiscr1 = 1,
    ExplicitDiscr2 = 5,
    ImplicitDiscrEmptyTuple(),
    ImplicitDiscrEmptyStruct {},
}

#[repr(u64)]
enum ImplicitReprs {
    A,
    B(),
    C {},
    D,
    E = 30,
    F,
    G,
    H {},
    I(),
}

fn f() -> u32 {
    const CONST: u16 = EnumWithRepr::ExplicitDiscr1 as u16;
    let _x = EnumWithRepr::ExplicitDiscr2 as u16;
    EnumWithRepr::ImplicitDiscrEmptyTuple() as u32
        + EnumWithRepr::ImplicitDiscrEmptyStruct {} as u32
}

fn get_repr(x: EnumWithRepr) -> u16 {
    x as u16
}

fn get_casted_repr(x: EnumWithRepr) -> u64 {
    x as u64
}
