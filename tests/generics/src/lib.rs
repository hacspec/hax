#![allow(dead_code)]

fn dup<T: Clone>(x: T) -> (T, T) {
    (x.clone(), x.clone())
}

fn foo<const LEN: usize>(arr: [usize; LEN]) -> usize {
    let mut acc = LEN + 9;
    for i in 0..LEN {
        acc += arr[i];
    }
    acc
}

fn repeat<const LEN: usize, T: Copy>(x: T) -> [T; LEN] {
    [x; LEN]
}
