mod for_loops {
    fn range1() -> usize {
        let mut acc = 0;
        for i in 0..15 {
            acc = acc + i;
        }
        acc
    }

    fn range2(n: usize) -> usize {
        let mut acc = 0;
        for i in 0..(n + 10) {
            acc = acc + i + 1;
        }
        acc
    }

    fn composed_range(n: usize) -> usize {
        let mut acc = 0;
        for i in (0..n).chain((n + 10)..(n + 50)) {
            acc = acc + i + 1;
        }
        acc
    }

    fn rev_range(n: usize) -> usize {
        let mut acc = 0;
        for i in (0..n).rev() {
            acc = acc + i + 1;
        }
        acc
    }

    fn chunks<const CHUNK_LEN: usize>(arr: Vec<usize>) -> usize {
        let mut acc = 0;
        let chunks = arr.chunks_exact(CHUNK_LEN);
        for chunk in chunks.clone() {
            let mut mean = 0;
            for item in chunk {
                mean = mean + item;
            }
            acc = acc + mean / CHUNK_LEN;
        }
        for item in chunks.remainder() {
            acc = acc - item;
        }
        acc
    }

    fn iterator(arr: Vec<usize>) -> usize {
        let mut acc = 0;
        for item in arr.iter() {
            acc = acc + item;
        }
        acc
    }

    fn nested(arr: Vec<usize>) -> usize {
        let mut acc = 0;
        for item in arr.iter() {
            for i in (0..*item).rev() {
                acc = acc + 1;
                for j in arr.iter().zip(4..i) {
                    acc = acc + item + i + j.0 + j.1;
                }
            }
        }
        acc
    }

    fn pattern(arr: Vec<(usize, usize)>) -> usize {
        let mut acc = 0;
        for (x, y) in arr {
            acc = acc + x * y;
        }
        acc
    }

    fn enumerate_chunks(arr: Vec<usize>) -> usize {
        let mut acc = 0;
        for (i, chunk) in arr.chunks(4).enumerate() {
            for (j, x) in chunk.iter().enumerate() {
                acc = i + j + x;
            }
        }
        acc
    }

    fn bool_returning(x: u8) -> bool {
        x < 10
    }

    fn f() {
        let mut acc = 0;
        for i in 1..10 {
            acc += i;
            bool_returning(i);
        }
    }
}
