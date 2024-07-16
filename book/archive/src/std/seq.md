# Sequence and array operations

## Operations common to sequences and arrays

### Base traits

Some operations are common to both [sequences and arrays](/book/language/seq.md)
by design, and can be used as the interoperability base between the two types
of collections. These operations are the following:
* `len`: gives the length of an array or sequence;
* `iter`: iterates over the content of the array or sequence
(unsafe in hacspec but can be used for implementing primitives)
* `create`: creates a sequence or array and initializes the elements to the
default value (0 for arithmetic types);
* `update_slice`, `update` and `update_start`: produce a new sequence or array
with modified contents.

Both sequences and arrays implement indexing with any type of unsigned public
integer.

### Chunking

Both arrays and sequences support chunking with methods like:
* `num_chunks` and `num_exact_chunks` (whole or partial blocks);
* `get_chunk`, `get_exact_chunk` and `get_remainder_chunk`;
* `set_chunk` and `set_exact_chunk`.

The read operations borrow the sequence or array, but the write operations
create a new sequence or array.

### Conversions

Sequences and arrays can be created from other types via methods like:
* `from_public_slice` and `from_slice`;
* `from_vec` and `from_native_slice`;
* `from_public_seq` and `from_seq` (to convert a seq into an array of the correct size);
* `from_string` and `from_hex` for byte or hex strings (hex only for `u8` sequences and arrays).

### Secrecy

The methods prefixed by `public` performs an element-wise classification of the
data under the hood.

### Ownage

Some methods have two versions: an `owned` and a non-`owned` version, depending
on whether the `self` argument is consumed or not by the method. This distinction
is useful to avoid unnecessary copies and thus be more performant.

## Array-specific operations

Since array length is known statically, `new` does not take any argument,
same as `length`. `slice`s of arrays become `Seq`.

## Sequence-specific operations

Sequences can be extended (by creating a new sequence under the hood) with
`push` or `concat`. Sequences can also be sliced with `slice`.
