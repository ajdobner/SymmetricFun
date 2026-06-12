# SymmetricFun

## Goal

Implement the ring of symmetric functions in Lean and prove some of its properties.

Note: some theorems about symmetric *polynomials* are already in `mathlib`. The implementation there is very dependent on the assumption that there are finitely many variables. To construct the ring of symmetric functions, one must either take some kind of categorical limit or take a subalgebra of a power series ring (in infinitely many variables). We will take the latter approach. 

**Plan**
1. Construct the ring of symmetric functions (and polynomials) as a subalgebra of the existing `MvPowerSeries` ring in `mathlib`.
    * Define the subalgebra of bounded degree series.
    * Define the action of permutations on `MvPowerSeries` and the subalgebra invariant under this action.
2. Prove that various families give bases for the ring of symmetric functions
    * monomial symmetric functions
    * Schur functions
    * elementary symmetric functions
    * complete homogeneous symmetric functions
    * power sum functions
3. Prove equivalences between different definitions of Schur functions: generating function for semistandard Young tableaux, Jacobi-Trudi identity, Weyl character formula. 
4. Prove the Pieri rules. 
5. Define the Hall inner product and the $\omega$ involution.
6. (Later?) Refactor `MvPowerSeries` so that it is constructed as a [total monoid algebra](https://en.wikipedia.org/wiki/Total_algebra). The monoid in this case is $(M,+)=\big((\mathbb{Z}_{\geq 0})^I,+\big)$ where $I$ represents the index set for the variables. Note: currently the `MvPolynomial` ring *is* implemented using a general monoid algebra construction.
Many properties of multivariate power series rings fit into this generalized setting.
    * A monoid homomorphism $M \to N$ induces an algebra homomorphism $R[[M]]\to R[[N]]$. An example of this in power series (or polynomial) ring setting occurs when one sends some of the variables to zero. 
    * A distributive group action on $M$ lifts to an action on $R[[M]]$. For example, for power series (or polynomials) we have an action of the symmetric group on the variables. The subset consisting of elements that are invariant under the action form a subalgebra by general principles.
7. (Hard) Prove positivity of Littlewood--Richardson coefficients, and/or the Littlewood--Richardson rule. Representation theory of $S_n$ and/or $GL_n$ are not implemented in `mathlib` so combinatorial proofs are probably better anyway.

