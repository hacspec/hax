use crate::prelude::*;
use rustc_lexer::TokenKind;
use std::fs;

/// Returns a list of (spanned) comments found in file `path`, or an
/// error if the file at `path` could not be open.
pub fn comments_of_file(path: PathBuf) -> std::io::Result<Vec<(Span, String)>> {
    fn clean_comment(comment: &str) -> &str {
        let comment = if let Some(comment) = comment.strip_prefix("/*") {
            comment
                .strip_suffix("*/")
                .expect("A comment that starts with `/*` should always ends with `*/`")
        } else {
            comment
                .strip_prefix("//")
                .expect("A comment has to start with `//` or `/*`")
        };
        comment.strip_prefix("!").unwrap_or(comment)
    }
    let source = &fs::read_to_string(&path)?;

    let mut comments = vec![];
    let (mut pos, mut line, mut col) = (0, 0, 0);
    for token in rustc_lexer::tokenize(source) {
        let len = token.len as usize;
        let sub = &source[pos..(pos + len)];
        let lo = Loc { line, col };
        line += sub.chars().filter(|c| matches!(c, '\n')).count();
        pos += len;
        if lo.line != line {
            col = sub.chars().rev().take_while(|c| !matches!(c, '\n')).count();
        } else {
            col += len;
        }

        if let TokenKind::LineComment { .. } | TokenKind::BlockComment { .. } = token.kind {
            if !sub.starts_with("///") && !sub.starts_with("/**") {
                let span = Span {
                    lo,
                    hi: Loc { line, col },
                    filename: FileName::Real(RealFileName::LocalPath(path.clone())),
                    rust_span_data: None,
                };
                comments.push((span, clean_comment(sub).to_string()));
            }
        }
    }
    Ok(comments)
}
