use hax_lib_macros as hax;

pub const MAX_MESSAGE_SIZE_LEN: usize = 128 + 64;
pub const CBOR_NEG_INT_1BYTE_START: u8 = 0x20u8;

#[hax::attributes]
pub struct EdhocMessageBuffer {
    pub content: [u8; MAX_MESSAGE_SIZE_LEN],
    #[refine(len <= MAX_MESSAGE_SIZE_LEN)]
    pub(crate) len: usize, // Note: visibility of `len` had to be restricted
}

impl EdhocMessageBuffer {
    pub fn new() -> Self {
        EdhocMessageBuffer {
            content: [0u8; MAX_MESSAGE_SIZE_LEN],
            len: 0,
        }
    }
}

pub struct EADItem {
    pub label: u8,
    pub is_critical: bool,
    pub value: Option<EdhocMessageBuffer>,
}

#[hax::requires(
    (!ead_1.is_critical || ead_1.label <= 255 - CBOR_NEG_INT_1BYTE_START)
 && (match ead_1.value {
       Some(ead_1_value) => ead_1_value.len < 192,
       None => true,
    })
)]
fn encode_ead_item(ead_1: &EADItem) -> EdhocMessageBuffer {
    let mut output = EdhocMessageBuffer::new();

    // encode label
    if ead_1.is_critical {
        // **Possible bug 1**: addition overflow
        output.content[0] = ead_1.label + CBOR_NEG_INT_1BYTE_START - 1;
    } else {
        output.content[0] = ead_1.label;
    }
    output.len = 1;

    // encode value
    if let Some(ead_1_value) = &ead_1.value {
        // **Possible bug 2**: out of bounds
        output.content[1..1 + ead_1_value.len]
            .copy_from_slice(&ead_1_value.content[..ead_1_value.len]);
        output.len += ead_1_value.len;
    }

    output
}
