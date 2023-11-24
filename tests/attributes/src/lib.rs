fn hello(x: &mut [u8]) {
    let y = &[10, 20, 30, 40];
    let mut aa = 3;
    aa += 1;
    for i in 0..x.len() {
        let lhs = x[i];
        let rhs = y[i];
        x[i] = lhs + rhs;
    }
}

fn main() -> u8 {
    let mut x: [u8; 4] = [1, 2, 3, 4];
    hello(&mut x);
    let x1 = x[1];
    let x0 = x[0];
    x[0] = x1 + x0;
    x[0]
}

// TODO list:
// plus_u8
