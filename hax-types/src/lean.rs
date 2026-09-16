/// Convert a crate name to CamelCase for Lean: split on `-` and `_`,
/// upper-case the first character of each segment, and concatenate. Not
/// injective: `my-crate`, `my_crate` and `my_Crate` all yield `MyCrate`.
pub fn to_camel_case(name: &str) -> String {
    name.split(['-', '_'])
        .map(|s| {
            let mut c = s.chars();
            match c.next() {
                None => String::new(),
                Some(f) => f.to_uppercase().to_string() + c.as_str(),
            }
        })
        .collect()
}
