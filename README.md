# Inverses
This is a collection of functions, proofs, and semantics made with Agda that I will use in making a programming language. This language's current goal is that all statements in it must always be able to be invertable, such that a previous program state can always be gotten back to.
This may involve:
1. All names being linearly typed to enforce no-information-loss
2. Some functions returning themselves to make sure their inverse can be called in any future program state.
3. If resources get implmented, they should be linear-typed. Having everything be linear-typed might make inverting easier, since information duplicaion&deduplication becomes explicit.
4. All functions are monadic with one inverse.
5. Higher order functions exist.
6. Functions can only be made with other functions that return guarenteed-invertable functions, given invertable functions.

The proofs made here are heavily inspired by Hans Hüttel's book "Transitions And Trees". I've translated some of [his book into Agda](https://github.com/Brian-ED/transition-and-trees/edit/master/README.md).
