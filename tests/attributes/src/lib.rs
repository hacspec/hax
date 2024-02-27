trait Foo {
    type X;
    const FOO: Self::X;
}

fn f<T: Foo<X = usize>>(x: T) -> usize {
    T::FOO + 3
}
