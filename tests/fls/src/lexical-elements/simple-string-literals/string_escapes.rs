//! @fls: fls_s76un78zyd0j, fls_7fuctvtvdi7x, fls_ycy5ee6orjx, fls_6nt5kls21xes, fls_1pdzwkt5txfj
//! @title: Simple string literals with plain characters and escapes
//! @lean(tier): supported
//! @lean(reason): aeneas fails on the string literals (`new value doesn't have the same type as its destination`); the types section of the input-language reference.

pub fn escaped() -> &'static str {
    "\x41\u{e9}\t'\"\\"
}

#[hax_test::equiv]
pub fn escapes_denote_characters() -> bool {
    escaped().as_bytes() == [0x41, 0xC3, 0xA9, 9, 39, 34, 92]
}
