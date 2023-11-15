use std::collections::HashSet;


fn insert_assert_len() {
    let mut s: HashSet<i32> = HashSet::new();
    assert!(s.len() == 0);

}

fn main() {
    insert_assert_len();
}
