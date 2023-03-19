use std::marker::PhantomData;
use std::ops::Add;

//use cortex_m_semihosting::{dbg, hprintln};
/// "RIOT"
const RIOTBOOT_MAGIC: u32 = 0x544f_4952;

/// Defines the required traits for the accumulator type
/// used in the algorithm
pub trait FletcherAccumulator<T>: Add<Self> + From<T> + From<<Self as Add>::Output> + Copy {
    /// Should return a reasonable default value
    ///
    /// Usual default values have the least significant bits set
    /// and the most significant bits cleared, i.e. 0x00ff
    fn default_value() -> Self;
    /// Should return the maximum number of words to sum before reducing
    ///
    /// This value should be the maximum summations that can happen before
    /// either accumulator overflows. This can be determined by
    /// putting the maximum word value into the algorithm and counting
    /// the number of words can be added before an overflow occurs.
    fn max_chunk_size() -> usize;
    /// Combines the two accumulator values into a single value
    ///
    /// This function can assume that the accumulators have already
    /// been fully reduced. This usually involves simply shifting
    /// the upper accumulator value into the MSB
    fn combine(lower: &Self, upper: &Self) -> Self;
    /// Reduces the accumulator value
    ///
    /// This function needs to reduce the accumulator value in a manner
    /// that rounds the value according to one's compliment math. This
    /// is usually accomplished with masking and shifting
    fn reduce(self) -> Self;
}

/// A generic type for holding intermediate checksum values
pub struct Fletcher<T, U> {
    a: T,
    b: T,
    phantom: PhantomData<U>,
}

impl<T, U> Fletcher<T, U>
where
    T: FletcherAccumulator<U>,
    U: Copy,
{
    pub fn new() -> Fletcher<T, U> {
        Fletcher {
            a: T::default_value(),
            b: T::default_value(),
            phantom: PhantomData,
        }
    }

    /// The core fletcher checksum algorithm
    ///
    /// The input data is processed in chunks which reduces the
    /// number of calls to `reduce()`. The size of the chunks depends
    /// on the accumulator size and data size.
    pub fn update(&mut self, data: &[U]) {
        let max_chunk_size = T::max_chunk_size();

        for chunk in data.chunks(max_chunk_size) {
            let mut intermediate_a = self.a;
            let mut intermediate_b = self.b;

            for byte in chunk {
                intermediate_a = T::from(intermediate_a + T::from(*byte));
                intermediate_b = T::from(intermediate_b + intermediate_a);
            }

            self.a = intermediate_a.reduce();
            self.b = intermediate_b.reduce();
        }

        // One last reduction must be done since we  process in chunks
        self.a = self.a.reduce();
        self.b = self.b.reduce();
    }

    /// Returns the current checksum value of the `Fletcher` object
    pub fn value(&self) -> T {
        T::combine(&self.a, &self.b)
    }
}

pub type Fletcher32 = Fletcher<u32, u16>;

impl FletcherAccumulator<u16> for u32 {
    fn default_value() -> Self {
        0x0000ffff
    }

    fn max_chunk_size() -> usize {
        360
    }

    fn combine(lower: &Self, upper: &Self) -> Self {
        lower | (upper << 16)
    }

    fn reduce(self) -> Self {
        (self & 0xffff) + (self >> 16)
    }
}

/// struct defining riotboot header
#[derive(Debug)]
#[repr(C)]
pub struct Header {
    /// Header magic number (always "RIOT")
    magic_number: u32,
    /// Integer representing the partition version
    sequence_number: u32,
    /// Address after the allocated space for the header
    start_addr: u32,
    /// Checksum of riotboot_hdr
    checksum: u32,
}

impl Header {
    fn as_u16_slice(&self) -> &[u16] {
        unsafe {
            ::core::slice::from_raw_parts(
                (self as *const Header) as *const u16,
                (::core::mem::size_of::<Header>() / 2) - 2, // assume checksum is last and two words long, and must be skipped.
            )
        }
    }
    pub fn is_valid(&self) -> bool {
        //hprintln!("magic: {:#08x}", self.magic_number).unwrap();
        if self.magic_number == RIOTBOOT_MAGIC {
            let mut fletcher = Fletcher32::new();
            fletcher.update(self.as_u16_slice());
            let sum = fletcher.value();
            //hprintln!("sum: {:#08x}", sum).unwrap();
            //hprintln!("expexted: {:#08x}", self.checksum).unwrap();
            return sum == self.checksum;
        }
        false
    }
}

pub fn choose_image(images: &[&Header]) -> Option<u32> {
    let mut image: Option<u32> = None;

    for header in images {
        if header.is_valid() {
            if let Some(image) = image {
                if header.sequence_number <= image {
                    continue;
                }
            }
            //hprintln!("found image").unwrap();
            //hprintln!("valid image address: {:#08x}", header.start_addr).unwrap();
            image = Some(header.start_addr)
        }
    }
    image
}

// #![test]
// mod test {
//     use super::*;

//     #[test]
//     test_
