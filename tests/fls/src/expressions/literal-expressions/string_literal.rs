//! @fls: fls_rbwwczom3agt, fls_w30su9x4q13r, fls_wdpbg5xzgmwu
//! @title: String literal expressions
//! @lean(tier): supported
//! @lean(reason): aeneas fails on a function returning a string literal (`There should be no bottoms in the value`).

pub fn text() -> &'static str {
    "text"
}

pub fn is_text(s: &str) -> bool {
    s == "text"
}

#[hax_test::equiv]
pub fn string_literal_value() -> bool {
    is_text(text()) && !is_text("other")
}
