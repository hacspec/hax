/// Issue #757
fn calling_function_pointer() {
    fn f<T>() {}
    let f_ptr = f::<i32>;
    f_ptr();
}
