/// This fails in inspect_local_def_id with attempted to read from stolen value
/// It has to
/// * be in a module
/// * use the constant
/// * use the generic type
/// * derive something

pub const HASH_LENGTH: usize = 32;

// The actual derive doesn't matter.
#[derive(Debug)]
pub struct HashOf<T> {
    _inner: [T; HASH_LENGTH],
}
