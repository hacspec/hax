trait Tr {
    type Ty<X>;
}

impl Tr for () {
    type Ty<X> = Option<X>;
}
