use hax_lib_macros as hax;

#[hax::modeled_by(FStar::IO::debug_print_string)]
pub fn f(line: String) {
    println!("{}", line)
}

#[hax::decreases((m, n))]
pub fn ackermann(m: u64, n: u64) -> u64 {
    match (m, n) {
        (0, _) => n + 1,
        (_, 0) => ackermann(m - 1, 1),
        _ => ackermann(m - 1, ackermann(m, n - 1)),
    }
}

#[hax::lemma_statement]
/// $`\forall n \in \mathbb{N}, \textrm{ackermann}(2, n) = 2 (n + 3) - 3`$
pub fn ackermann_property_m1(n: u64) -> bool {
    ackermann(2, n) == 2 * (n + 3) - 3
}

#[hax::requires(x.len() == y.len() && forall(|i: usize| i >= x.len() || y[i] > 0))]
pub fn div_pairwise(x: Vec<u64>, y: Vec<u64>) -> Vec<u64> {
    x.iter()
        .copied()
        .zip(y.iter().copied())
        .map(|(x, y)| x / y)
        .collect()
}

#[hax::ensures(|result| result == x * 2)]
pub fn twice(x: u64) -> u64 {
    x + x
}

#[hax::attributes]
pub mod foo {
    pub struct Hello {
        pub x: u32,
        #[refine(y > 3)]
        pub y: u32,
        #[refine(y + x + z > 3)]
        pub z: u32,
    }
    impl Hello {
        pub fn sum(&self) -> u32 {
            self.x + self.y + self.z
        }
        #[ensures(|result| result - n == self.sum())]
        pub fn plus(self, n: u32) -> u32 {
            self.sum() + n
        }
    }
}
