//! @fls: fls_4nkzidytpi6, fls_bync24y6gp93, fls_sup43es8ps8r, fls_tw36n3g32a0y
//! @title: Destructors with an observable effect run in reverse declaration order
//! @lean(tier): unsupported
//! @lean(reason): The ownership model of the input-language reference: a destructor whose body has an observable effect has no faithful reading, since the value model has no effect at scope exit to attach it to. charon emits the `Drop` statement with the destructor, aeneas evaluates the statement as a no-op and never calls the user's `drop`, and only the elaboration of the `Drop` implementation stops the extraction (`Type mismatch: CoreOpsDropDrop.drop has type Logger → RustM (Logger × (Logger → Logger))`); a destructor over owned state would pass with its effect lost.

pub struct Logger<'a> {
    pub log: &'a mut [u8; 4],
    pub len: &'a mut usize,
    pub tag: u8,
}

impl Drop for Logger<'_> {
    fn drop(&mut self) {
        self.log[*self.len] = self.tag;
        *self.len += 1;
    }
}

pub fn run() -> [u8; 4] {
    let mut log = [0u8; 4];
    let mut len = 0;
    {
        let mut second_len = 0;
        let mut second_log = [0u8; 4];
        let _a = Logger {
            log: &mut second_log,
            len: &mut second_len,
            tag: 1,
        };
    }
    {
        let (mut l1, mut l2) = (0usize, 0usize);
        let (mut g1, mut g2) = ([0u8; 4], [0u8; 4]);
        let _first = Logger {
            log: &mut g1,
            len: &mut l1,
            tag: 1,
        };
        let _second = Logger {
            log: &mut g2,
            len: &mut l2,
            tag: 2,
        };
    }
    let _tail = Logger {
        log: &mut log,
        len: &mut len,
        tag: 9,
    };
    [1, 2, 3, 4]
}

#[hax_test::equiv]
pub fn program_runs() -> bool {
    run() == [1, 2, 3, 4]
}
