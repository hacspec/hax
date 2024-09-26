struct Inner {
    value: u8,
}

struct Container {
    value: u8,
    inner: Inner,
}

impl Inner {
    pub fn update(&mut self, new: u8) {
        self.value = new;
    }
}

impl Container {
    /// error: [HAX0010] (RefMut) At this position, Hax was expecting an
    /// expression of the shape `&mut _`. Hax forbids `f(x)` (where `f` expects
    /// a mutable reference as input) when `x` is not a place expression[1] or
    /// when it is a dereference expression.
    ///
    /// [1]: https://doc.rust-lang.org/reference/expressions.html#place-expressions-and-value-expressions
    pub fn mutable_value(&mut self) -> &mut Inner {
        &mut self.inner
    }

    pub fn mutable_match(&mut self) {
        /// error: [HAX0003] (RefMut) The mutation of this &mut is not allowed here.
        match &mut self.inner {
            _ => unimplemented!(),
        }
    }

    pub fn use_mutable_member(&mut self) {
        // This is fine
        self.inner.update(5);
        // error: [HAX0003] (RefMut) The mutation of this &mut is not allowed here.
        let inner = self.mutable_value();
        // error: [HAX0010] (RefMut) At this position, Hax was expecting an
        // expression of the shape `&mut _`. Hax forbids `f(x)` (where `f`
        // expects a mutable reference as input) when `x` is not a place
        // expression[1] or when it is a dereference expression.
        //
        // [1]: https://doc.rust-lang.org/reference/expressions.html#place-expressions-and-value-expressions
        inner.update(5);
    }

    pub fn break_continue(self) {
        // error: [HAX0001] (FunctionalizeLoops) something is not implemented yet.
        // Loop without mutation?
        for x in 0..5 {
            if x == 1 {
                // error: [HAX0008] (reject_Continue) ExplicitRejection { reason: "a node of kind [Continue] have been found in the AST" }
                continue;
            }
            if x == 3 {
                // error: [HAX0001] (CfIntoMonads) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/96.
                // Please upvote or comment this issue if you see this error message.
                // TODO: Monad for loop-related control flow
                break;
            }
        }
    }
}
