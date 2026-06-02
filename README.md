# SymmetricFun

## Goal

Implement the ring of symmetric functions in Lean and prove some of its properties.
* Some facts about symmetric polynomials are implemented in `mathlib`. These only work for finitely many variables. The infinite variable case requires taking some kind of categorical limit or using subalgebras of power series rings.
* Currently `mathlib` implements multivariate polynomial rings $R[x_i : i \in I]$ using a general monoid algebra construction. Symmetric polynomials are then implemented as a subalgebra. Power series rings $R[[x_i : i \in I]]$ are also implemented, but not using any general machinery. The latter could be generalized via the **total monoid algebra** construction $R[[M]]$, which is not implemented in Lean.

**Plan**
1. Initially construct the ring of symmetric functions (and polynomials) as a subalgebra of the existing `MvPowerSeries` ring in `mathlib`.
2. Define various bases for the ring of symmetric functions: monomial, elementary, complete homogeneous, Schur, power sum.
    * For Schur functions this requires choosing one of the definitions. Probably it's best to use semistandard Young tableau definition?
3. Prove the fundamental theorem of symmetric functions. This is proved already in the finite variable case.
4. Define the Hall inner product and the $\omega$ involution.
4. Prove the Pieri rules. 
4. (Later?) Refactor `MvPowerSeries` to use the total monoid algebra construction. One advantage here is that *specialization* in power series (or polynomial) rings is an instance of a more general construction: if $M \to N$ is a monoid homomorphism then this induces a homomorphism $R[[M]]\to R[[N]]$. Specialization is useful for proving the categorical limit properties of symmetric functions.
4. (Hard) Prove positivity of Littlewood--Richardson coefficients, and/or the Littlewood--Richardson rule. Representation theory of $S_n$ and/or $GL_n$ are not implemented in `mathlib` so combinatorial proofs are probably better anyway.

