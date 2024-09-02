#![allow(dead_code)]

pub fn asserts() {
    assert!({
        assert!(true);
        1 == 1
    });
    assert_eq!(2, 2);
    assert_ne!(1, 2);
}
