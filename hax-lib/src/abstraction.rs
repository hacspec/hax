/// Marks a type as abstractable: its values can be mapped to an
/// idealized version of the type. For instance, machine integers,
/// which have bounds, can be mapped to mathematical integers.
///
/// Each type can have only one abstraction.
pub trait Abstraction {
    /// What is the ideal type values should be mapped to?
    type AbstractType;
    /// Maps a concrete value to its abstract counterpart
    fn lift(self) -> Self::AbstractType;
}

/// Marks a type as abstract: its values can be lowered to concrete
/// values. This might panic.
pub trait Concretization<T> {
    /// Maps an abstract value and lowers it to its concrete counterpart.
    fn concretize(self) -> T;
}
