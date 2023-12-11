# Experiments with Flix

This is a small collection of experiments with [Flix](https://flix.dev/). Flix is a functional programming language—a bit like Haskell or Scala, but with some Rust-like design choices. But the most interesting part of Flix is that it includes a rather interesting Datalog dialect:

- **First class sets of relations.** You can build relations at runtime, compose them, and pass them around. This is fully integrated into the type system using row types.
- **Stratified negation.** Negation with guaranteed termination.
- **Fixpoints and lattices.** This offers a really interesting model, where you can infer facts about the world, and then combine them using a least upper bound over a lattice.

Anyway, some of this code is prototypes for other open source projects, a bits of it might turn into blog posts.

