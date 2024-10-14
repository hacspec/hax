mod typ_a {
    pub enum TRec {
        T(super::typ_b::T1Rec),
        Empty,
    }
    pub enum T {
        T(super::typ_b::T1),
    }
}
mod typ_b {
    pub enum T1Rec {
        T1(Box<T2Rec>),
    }
    pub enum T2Rec {
        T2(super::typ_a::TRec),
    }

    pub enum T1 {
        T1,
    }
    pub enum T2 {
        T2(super::typ_a::T),
    }
}

fn f() {}
mod b {
    pub fn g() {
        super::f()
    }
}
fn h() {
    b::g();
    c::i()
}
fn h2() {
    c::i()
}
mod c {
    pub fn i() {}
}
mod d {
    pub fn d1() {}
    pub fn d2() {
        super::de::de1()
    }
}
mod e {
    pub fn e1() {
        super::d::d1()
    }
}
mod de {
    pub fn de1() {
        super::e::e1()
    }
}

mod rec {
    enum T {
        t1,
        t2,
    }
    pub fn g1(x: T) -> T {
        match x {
            T::t1 => g2(x),
            T::t2 => T::t1,
        }
    }
    pub fn g2(x: T) -> T {
        match x {
            T::t1 => g1(x),
            T::t2 => hf(x),
        }
    }
    pub fn hf(x: T) -> T {
        match x {
            T::t1 => hf(T::t2),
            T::t2 => x,
        }
    }
}

mod rec1_same_name {
    pub fn f(x: i32) -> i32 {
        super::rec2_same_name::f(x)
    }
}
mod rec2_same_name {
    pub fn f(x: i32) -> i32 {
        if x > 0 {
            super::rec1_same_name::f(x - 1)
        } else {
            0
        }
    }
}
mod enums_a {
    pub enum T {
        A,
        B,
        C(Vec<super::enums_b::U>),
        D(Vec<super::enums_b::T>),
    }
}
mod enums_b {
    pub enum U {
        A,
        B,
        C(Vec<super::enums_a::T>),
    }
    pub enum T {
        A,
        B,
        C(Vec<super::enums_a::T>),
    }
    pub fn f() -> T {
        T::A
    }
}

mod m1 {
    pub fn a() {
        super::m2::c()
    }
}

mod m2 {
    pub fn d() {}
    pub fn b() {
        super::m1::a();
        d()
    }
    pub fn c() {}
}
