enum Instruction {
    Push(isize),
    Pop,
    Add,
    Sub,
    Mul,
    Not,
    Dup,
}

impl Instruction {
    pub fn interpret(self, stack: &mut Vec<isize>) {
        match self {
            Instruction::Push(v) => stack.push(v),
            Instruction::Pop => {
                stack.pop();
            }
            Instruction::Add => match (stack.pop(), stack.pop()) {
                (Some(a), Some(b)) => stack.push(b + a),
                _ => (),
            },
            Instruction::Sub => match (stack.pop(), stack.pop()) {
                (Some(a), Some(b)) => stack.push(b - a),
                _ => (),
            },
            Instruction::Mul => match (stack.pop(), stack.pop()) {
                (Some(a), Some(b)) => stack.push(b * a),
                _ => (),
            },
            Instruction::Not => match stack.pop() {
                Some(a) => stack.push(if a == 0 { 1 } else { 0 }),
                _ => (),
            },
            Instruction::Dup => match stack.pop() {
                Some(a) => {
                    stack.push(a);
                    stack.push(a);
                }
                _ => (),
            },
        }
    }
}

fn example() -> Vec<isize> {
    let mut stk = Vec::new();
    for cmd in [
        Instruction::Push(1),
        Instruction::Push(1),
        Instruction::Add,
        Instruction::Push(1),
        Instruction::Push(1),
        Instruction::Push(1),
        Instruction::Add,
        Instruction::Add,
        Instruction::Dup,
        Instruction::Mul,
        Instruction::Sub,
    ] {
        cmd.interpret(&mut stk)
    }
    stk
}
// Push 1: 1
// Push 1: 1, 1
//    Add: 2
// Push 1: 2, 1
// Push 1: 2, 1, 1
// Push 1: 2, 1, 1, 1
//    Add: 2, 1, 2
//    Add: 2, 3
//    Dup: 2, 3, 3
//    Mul: 2, 9
//    Sub: -7
