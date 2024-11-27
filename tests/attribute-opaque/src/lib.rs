#[hax_lib::opaque_type]
struct OpaqueStruct<const X: usize, T, U> {
    field: [T; X],
    other_field: U,
}

#[hax_lib::opaque_type]
enum OpaqueEnum<const X: usize, T, U> {
    A([T; X]),
    B(U),
}

#[hax_lib::opaque]
fn f(x: bool, y: bool) -> bool {
    x && y
}
trait T {
    fn d();
}

#[hax_lib::opaque]
impl T for u8 {
    fn d() {
        unsafe {
            let my_num: i32 = 10;
            let my_num_ptr: *const i32 = &my_num;
            let mut my_speed: i32 = 88;
            let my_speed_ptr: *mut i32 = &mut my_speed;
        }
    }
}

#[hax_lib::opaque]
const c: u8 = { 0 + 0 };
