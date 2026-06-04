# SymmetricFun

## Goal

Implement the ring of symmetric functions in Lean and prove some of its properties.
* Some facts about symmetric polynomials are implemented in `mathlib`. These only work for finitely many variables. The infinite variable case requires taking some kind of categorical limit or using subalgebras of power series rings.
* Currently `mathlib` implements multivariate polynomial rings $R[x_i : i \in I]$ using a general monoid algebra construction. Symmetric polynomials are then implemented as a subalgebra. Power series rings $R[[x_i : i \in I]]$ are also implemented, but not using any general machinery. The latter could be generalized via the [total monoid algebra](https://en.wikipedia.org/wiki/Total_algebra) construction $R[[M]]$, which is not implemented in Lean.

**Plan**
1. Construct the ring of symmetric functions (and polynomials) as a subalgebra of the existing `MvPowerSeries` ring in `mathlib`.
    (a) Define the subalgebra of bounded degree series.
    (b) Define the action of permutations on `MvPowerSeries` and the subalgebra invariant under this action.
2. Define various bases for the ring of symmetric functions: monomial, elementary, complete homogeneous, Schur, power sum.
3. Prove the fundamental theorem of symmetric functions. The finite variable case is already done in `mathlib`.
4. Prove equivalences between different definitions of Schur functions: generating function for semistandard Young tableaux, Jacobi-Trudi identity, Weyl character formula. 
5. Prove the Pieri rules. 
6. Define the Hall inner product and the $\omega$ involution.
7. (Later?) Refactor `MvPowerSeries` to use the total monoid algebra construction. The monoid in this case is $(M,+)=\big((\mathbb{Z}_{\geq 0})^I,+\big)$ where $I$ represents the index set for the variables. Many properties of multivariate power series rings fit into this generalized setting.
    * A monoid homomorphism $M \to N$ induces an algebra homomorphism $R[[M]]\to R[[N]]$. An example of this in power series (or polynomial) ring setting occurs when one sends some of the variables to zero. 
    * A distributive group action on $M$ lifts to an action on $R[[M]]$. For example, for power series (or polynomials) we have an action of the symmetric group on the variables. The subset consisting of elements that are invariant under the action form a subalgebra by general principles.
8. (Hard) Prove positivity of Littlewood--Richardson coefficients, and/or the Littlewood--Richardson rule. Representation theory of $S_n$ and/or $GL_n$ are not implemented in `mathlib` so combinatorial proofs are probably better anyway.

