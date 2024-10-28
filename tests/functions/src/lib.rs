/// Issue #757
fn calling_function_pointer() {
    fn f<T>() {}
    let f_ptr = f::<i32>;
    f_ptr();
}

mod issue_1048 {
    pub struct CallableViaDeref;

    impl core::ops::Deref for CallableViaDeref {
        type Target = fn() -> bool;

        fn deref(&self) -> &Self::Target {
            &((|| true) as fn() -> bool)
        }
    }

    pub fn call_via_deref() -> bool {
        CallableViaDeref()
    }
}
