---
authors:
  - maxime
title: "Hax for everyone"
date: 2025-02-20
---

# Trying to make hax usable in more contexts
The hax toolchain has been successfully used to formally verify our cryptographic implementations for [ML-KEM](https://cryspen.com/post/ml-kem-verification/),[Bertie](https://cryspen.com/post/hax-pv/) and more. All these projects are developed with formal verification (using hax) in mind, and use a limited number of Rust features.
However, hax is under constant development and the improvements we bring are targeted at making it more usable. With these improvements we want to bring hax to a new kind of projects that don’t have restrictions on the Rust patterns they use. We want hax to be usable in this context with minimal modifications to the code (ideally no modification at all). An example of such a project is the verification of [sandwich](https://github.com/sandbox-quantum/sandwich), a high-level cryptographic library that we are working on together with [SandboxAQ](https://cryspen.com/post/hax-sandbox/). This project revealed the weaknesses of hax in this context which brought us to implement some improvements that will be presented in this blog post.
## Challenges
The projects that use hax from the beginning can limit themselves to the subset of Rust supported by hax. Applying hax to a pre-existing project means some large parts are probably not supported. The challenge is then to identify which features to prioritize for support in hax (and adding support is yet another challenge), and which features have no short-term plan for support (mainly mutable references and raw pointers). For the latter we need to abstract out the code (if it is not relevant for proofs) or rewrite it (when possible, and ideally we should avoid this).
Having external users encourages us even more to make hax an easily-usable and well-documented tool.
## Frontend improvements
The hax frontend is mostly relying on rustc and cargo to extract intermediary representations of a Rust crate. It is supposed to produce a result for any Rust crate (restrictions on the available Rust features come later in the toolchain). However the information given by rustc is sometimes partial or lacks some parts that are needed for our translations. A crucial example of this is trait resolution as we need to know the trait derivation that is used by each call of a trait method. This is a part of the hax frontend that has proven tricky and still had many bugs a few months ago. At that time, launching it on a somehow complicated crate had big chances of resulting in a crash. As part of our effort to improve the usability of hax, many of these bugs have now been fixed which is a great step forward, especially as even for some projects that look simple, we need to extract part of the dependencies which are usually more problematic.
According to our tests on the top 500 crates (by number of downloads on crates.io), hax frontend succeeds without crashing or timing out on more than 99%. However we are still looking for a better way to measure the coverage of the Rust features, and identifying the situations where we can still improve.
## Recursive Bundles
Rust modules are more of a namespacing system than an actual module system as used in functional languages (like our backends). In particular our backends require the module dependency graph to be acyclic while Rust has no such restriction. It is quite common in Rust to \make use of this and create cyclic dependencies between modules which means it is necessary for us to have a solution for this problem.
Here is an example (you can open it in the hax playground to check the code hax generates out of it):
```rust

pub struct Error();

mod private {
	pub(crate) fn f() -> Result<(), super::Error> {
    	Ok(())
	}
}

pub fn user_f() -> Result<(), Error> {
	private::f()
}
```
[Open this code snippet in the hax playground](https://hax-playground.cryspen.com/#fstar/b7fe08cccd/gist=fcb9cb9854c69ee6e2788648a380ff79)

In this example there is a dependency between the top level module and the `private` module. Our solution to break these cycles is simply to put the content of the cyclic modules in a single module (that we call bundle), and then re-exposing the items in their original modules.
This solution is not perfect because it changes the architecture of the generated code compared to the original code, and it could be improved by minimizing the content of the bundles (choosing a set of definitions to break the cycle instead of the full content of the modules). But so far it has proven very useful as it removes a big limitation on the Rust we support.
## Opaque items
Large projects usually contain code that we don’t support yet but we still want to reason about the rest of the project and have an abstract model (axiomatization) for the parts that we don’t support. We need to control which parts we want to fully extract and which parts we extract only as axioms. CLI include flags have been the solution for this but they only allow to choose at the model level, which is inconvenient for large projects. To make this more practical we added another way to specify inside the source with the attribute `hax_lib::opaque` makes an item axiomatized. There is still the problem of complicated `-i` flags which will be solved in the future by having the corresponding information in configuration files.
## Control flow rewriting without monads including inside loops
Translating imperative code to functional backends for verification implies some handling of side effects and transformation of control flow. A classic solution for this is to have a monadic encoding state which results in generated code that can be hard to read (and to reason about). This is the solution that was implemented (with some bugs) in hax but we decided to replace it with a solution without monads. The code we produce is simpler to read, but the main limitation is that there is code duplication which in some cases can lead to an extracted code that is exponentially bigger than the source.

Here is a simple example of this:
```rust
fn f() -> i32{
	if true {
    	if true {
        	return 1
    	}
	}
	3
}
```
[Open this code snippet in the hax playground](https://hax-playground.cryspen.com/#fstar/b7fe08cccd/gist=078ca6da8dad17541533bb5a0724784b)

The F* code extracted from this example is the following:
```ocaml
let f (_: Prims.unit) : i32 =
 if true
 then if true then mk_i32 1 else mk_i32 3
 else mk_i32 3
```
Here the semantics is preserved, but adding the `else` branches results in a duplication of the return value `3`.
Our idea to improve in the future is to revive the monadic version, but use it only if the duplication is too big. 
Support for control flow (`return`, `break` and `continue`) in loops has been added as well. In hax, loops are translated as a functional fold in which the accumulator keeps track of the modification of the environment done by the effectful operations in the source. This extension relies on a monadic encoding of the loop result, that is passed in the accumulator to deal with the specific cases of `return`, `break` and `continue`. 
## Items sorting
A quality of life feature that we have been lacking for a long time is trying to respect, as much as possible, the same order of items in the generated code compared to the source. We need to modify the order because (as for modules), Rust allows items to be defined in any order, while our backends need items to be defined after the other items they depend on (except for mutual recursion). We rely on a graph topological sort to ensure this property, and now use a modified version of the stable topological sort provided by ocamlgraph, which produces an order that respects the dependencies, but in the absence of constraints tries respects the order of the source.
## Conclusion
Bringing hax to a new kind of project revealed the gap needed for it to be usable, but thanks to our active work, we have made great progress towards this goal. Even though there is still much more to do, this has allowed us to get results in these new applications of hax (stay tuned for more details about that!).
