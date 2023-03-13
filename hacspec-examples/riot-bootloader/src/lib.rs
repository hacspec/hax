use hacspec_lib::*;

/// "RIOT"
const RIOTBOOT_MAGIC: u32 = 0x544f_4952u32;

/// A generic type for holding intermediate checksum values
type Fletcher = (u32, u32);

pub fn new_fletcher() -> Fletcher {
    (0x0000_ffffu32, 0x0000_ffffu32)
}

pub fn max_chunk_size() -> usize {
    360
}

fn reduce_u32(x: u32) -> u32 {
    (x & 0xffffu32) + (x >> 16u32)
}

fn combine(lower: u32, upper: u32) -> u32 {
    lower | (upper << 16u32)
}

pub fn update_fletcher(f: Fletcher, data: Seq<u16>) -> Fletcher {
    let max_chunk_size = max_chunk_size();
    let (mut a, mut b) = f;

    for i in 0..data.num_chunks(max_chunk_size) {
        let (chunk_len, chunk) = data.get_chunk(max_chunk_size, i);
        let mut intermediate_a = a;
        let mut intermediate_b = b;

        for j in 0..chunk_len {
            intermediate_a = intermediate_a + chunk[j] as u32;
            intermediate_b = intermediate_b + intermediate_a;
        }

        a = reduce_u32(intermediate_a);
        b = reduce_u32(intermediate_b);
    }

    a = reduce_u32(a);
    b = reduce_u32(b);
    (a, b)
}

/// Returns the current checksum value of the `Fletcher` object
pub fn value(x: Fletcher) -> u32 {
    let (a, b) = x;
    combine(a, b)
}

/// 1. Header magic number (always "RIOT")
/// 2. Integer representing the partition version
/// 3. Address after the allocated space for the header
/// 4. Checksum of riotboot_hdr
type Header = (u32, u32, u32, u32);

fn header_as_u16_slice(h: Header) -> Seq<u16> {
    let (magic, seq_number, start_addr, _) = h;
    let magic = u32_to_be_bytes(magic);
    let seq_number = u32_to_be_bytes(seq_number);
    let start_addr = u32_to_be_bytes(start_addr);
    let u8_seq = Seq::<u8>::new(12);
    let u8_seq = u8_seq.update_slice(0, &magic, 0, 4);
    let u8_seq = u8_seq.update_slice(4, &seq_number, 0, 4);
    let u8_seq = u8_seq.update_slice(8, &start_addr, 0, 4);
    let mut u16_seq = Seq::<u16>::new(6);
    for i in 0..3 {
        let u16_word = u16Word::from_seq(&u8_seq.slice(i * 4, 2));
        let u16_value = u16_from_be_bytes(u16_word);
        u16_seq[2 * i + 1] = u16_value;
        let u16_word = u16Word::from_seq(&u8_seq.slice(i * 4 + 2, 2));
        let u16_value = u16_from_be_bytes(u16_word);
        u16_seq[2 * i] = u16_value;
    }
    u16_seq
}
pub fn is_valid_header(h: Header) -> bool {
    let (magic_number, seq_number, start_addr, checksum) = h;
    let slice = header_as_u16_slice((magic_number, seq_number, start_addr, checksum));
    let mut result = false;
    if magic_number == RIOTBOOT_MAGIC {
        let fletcher = new_fletcher();
        let fletcher = update_fletcher(fletcher, slice);
        let sum = value(fletcher);
        result = sum == checksum;
    }
    result
}

pub fn choose_image(images: Seq<Header>) -> (bool, u32) {
    let mut image = 0u32;
    let mut image_found = false;

    for i in 0..images.len() {
        let header = images[i];
        let (magic_number, seq_number, start_addr, checksum) = header;
        if is_valid_header((magic_number, seq_number, start_addr, checksum)) {
            let change_image = !(image_found && (seq_number <= image));
            if change_image {
                image = start_addr;
                image_found = true;
            }
        }
    }
    (image_found, image)
}
