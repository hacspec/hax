enum Foo<'a, T, const N : usize> {
    Bar(u8),
    Baz,
    Qux {x : &'a T, y : [T; N], z : u8},
}

fn test() {
    {
        enum AnimalA {
            Dog,
            Cat,
        }

        let mut a: AnimalA = AnimalA::Dog;
        a = AnimalA::Cat;
    }

    {
        enum AnimalB {
            Dog(String, f64),
            Cat { name: String, weight: f64 },
        }

        let mut a: AnimalB = AnimalB::Dog("Cocoa".to_string(), 37.2);
        a = AnimalB::Cat { name: "Spotty".to_string(), weight: 2.7 };
    }
    {
        enum Examples {
            UnitLike,
            TupleLike(i32),
            StructLike { value: i32 },
        }

        use Examples::*; // Creates aliases to all variants.
        let x = UnitLike; // Path expression of the const item.
        let x = UnitLike {}; // Struct expression.
        let y = TupleLike(123); // Call expression.
        let y = TupleLike { 0: 123 }; // Struct expression using integer field names.
        let z = StructLike { value: 123 }; // Struct expression.
    }
    {
        #[repr(u8)]
        enum Enum {
            Unit = 3,
            Tuple(u16),
            Struct {
                a: u8,
                b: u16,
            } = 1,
        }
    }
}
