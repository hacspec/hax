#[hax_lib::opaque]
struct OpaqueStruct<const X: usize, T, U> {
    field: [T; X],
    other_field: U,
}

#[hax_lib::opaque]
enum OpaqueEnum<const X: usize, T, U> {
    A([T; X]),
    B(U),
}

#[hax_lib::opaque]
fn f_generic<const X: usize, T, U>(x: U) -> OpaqueEnum<X, T, U> {
    OpaqueEnum::B(x)
}

#[hax_lib::opaque]
fn f(x: bool, y: bool) -> bool {
    x && y
}

#[hax_lib::opaque]
#[hax_lib::requires(x)]
#[hax_lib::ensures(|result| result == y)]
fn f_pre_post(x: bool, y: bool) -> bool {
    x && y
}

#[hax_lib::attributes]
trait T {
    type U;
    const c: u8;
    fn d();
    #[hax_lib::requires(x == 0)]
    fn m(&self, x: u8) -> bool;
}

#[hax_lib::attributes]
#[hax_lib::opaque]
impl T for u8 {
    type U = u8;
    const c: u8 = 0;
    fn d() {
        unsafe {
            let my_num: i32 = 10;
            let _my_num_ptr: *const i32 = &my_num;
            let mut my_speed: i32 = 88;
            let _my_speed_ptr: *mut i32 = &mut my_speed;
        }
    }
    #[hax_lib::requires(x == 0)]
    #[hax_lib::ensures(|result| result)]
    fn m(&self, x: u8) -> bool {
        *self >= x
    }
}

trait TrGeneric<U: Clone> {
    fn f(x: U) -> Self;
}

#[hax_lib::opaque]
impl<U: Clone> TrGeneric<U> for i32 {
    fn f(_x: U) -> Self {
        0
    }
}

#[hax_lib::opaque]
const C: u8 = 0 + 0;

struct S1();

impl S1 {
    #[hax_lib::opaque]
    fn f_s1() {}
}

struct S2();

#[hax_lib::opaque]
impl S2 {
    fn f_s2() {}
}
