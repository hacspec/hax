fn f(x: &usize) -> usize {
    *x
}
fn g(x: &&usize) -> usize {
    f(*x)
}
