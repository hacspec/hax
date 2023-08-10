#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(hax)]

/** TypeAlias:BlockDocComment Lorem ipsum dolor sit amet, consectetur
adipiscing elit. Integer bibendum, massa quis facilisis aliquam,
dui libero auctor sem, aliquet dignissim urna magna ac turpis. */
#[hax::a::path(TypeAlias attr)]
type TypeAlias<#[hax::a::path(TypeAlias:T attr)] T: Clone> = (T, u8);

/// f:LineBlockComment
#[hax::a::path(f attr)]
fn f<#[hax::a::path(f:T attr)] T, #[hax::a::path(f:Y attr)] const Y: usize>(_x: T) -> usize {
    Y
}

#[hax::a::path(Foo attr)]
enum Foo {
    #[hax::a::path(Foo:A attr)]
    A(
        #[hax::a::path(Foo:A:u8 attr)] u8,
        #[hax::a::path(Foo:A:u16 attr)] u16,
    ),
    #[hax::a::path(Foo:B attr)]
    B {
        /// some Foo::B::x comment
        #[hax::a::path(Foo:B:x attr)]
        x: u8,
        /// some Foo::B::y comment
        #[hax::a::path(Foo:B:y attr)]
        y: u16,
    },
}

#[hax::a::path(Bar attr)]
struct Bar {
    #[hax::a::path(Bar:field1 attr)]
    field1: u64,
    /** some Bar::field2 comment Quisque et purus lacinia, venenatis
       risus eu, hendrerit arcu. Nunc posuere iaculis mattis. Sed at
       enim justo. Praesent aliquet ipsum in enim mollis
       faucibus. Morbi eu diam molestie, posuere quam eget, pulvinar
       diam.
    */
    #[hax::a::path(Bar:field2 attr)]
    field2: u32,
}
