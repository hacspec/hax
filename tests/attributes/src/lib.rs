struct Wrapped {
    contents: [u8; 10],
}

fn wrapped(x: &mut Wrapped) {
    x.contents[3] = 3;
}

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

fn pure(x: u8, y: u8) -> u8 {
    x + y + y + x
}

fn allocating(x: u8, y: u8) -> [u8; 2] {
    [x, y]
}

fn main(unit: ()) -> u8 {
    let mut x: [u8; 4] = [1, 2, 3, 4];
    hello(&mut x);
    let x1 = x[1];
    let x0 = x[0];
    x[0] = x1 + x0;
    x[0]
}

// TODO list:
// plus_u8 (monophization) (low priority)
// heurstic type ->
//   non-array inputs & output -> Tot
//   array input but non-array output -> Stack
//   any input & array output -> StackInline
