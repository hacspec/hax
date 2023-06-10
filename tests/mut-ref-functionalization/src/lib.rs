fn _f() {
    let mut vec = Vec::new();
    vec.push(1);
    vec.push(2);
    vec.swap(0, 1);
}

fn build_vec() -> Vec<u8> {
    vec![1, 2, 3]
}

fn _append() {
    let mut vec1 = Vec::new();
    let mut vec2 = vec![1u8, 2, 3];
    // This works
    vec1.append(&mut vec2);
    // This doesn't work
    vec1.append(&mut build_vec());
}
