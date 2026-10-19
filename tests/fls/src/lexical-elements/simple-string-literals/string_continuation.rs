//! @fls: fls_s76un78zyd0j, fls_7fuctvtvdi7x, fls_ycy5ee6orjx, fls_wawtu6j3fiqn
//! @title: A string continuation that drops the line break and the leading whitespace
//! @lean(tier): supported
//! @lean(reason): aeneas fails on the string literals (`new value doesn't have the same type as its destination`); the types section of the input-language reference.

pub fn continued() -> &'static str {
    "ab\
     cd"
}

#[hax_test::equiv]
pub fn continuation_joins_lines() -> bool {
    continued() == "abcd"
}
