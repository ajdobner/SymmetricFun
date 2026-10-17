# SymmetricFun

## Goal

Implement the ring of symmetric functions in Lean and prove some of its properties.

**Note:** some theorems about symmetric *polynomials* are already in `mathlib`. The implementation there is very dependent on the assumption that there are finitely many variables. To construct the ring of symmetric functions, one must either take some kind of categorical limit or take a subalgebra of a power series ring (in infinitely many variables).


Mathematically speaking, we construct the ring of symmetric functions within the larger ring of multivariate power series (with infinitely many variables). More specifically, one considers (say) the ring $R[[X_1,X_2,...]]$ and then takes the subalgebra consisting of those elements satisfying (1) they have bounded total degree, and (2) they are invariant under permuting the variables.

## How do we achieve this in Lean

The multivariate power series ring is already implemented in `mathlib` as `MvPowerSeries σ R`. Here `R` is the coefficient ring and `σ` is the type that indexes the variables.

What have we added to `MvPowerSeries`?
* `Homogeneous.lean` develops some machinery related to the submodules consisting of homogeneous elements
* `BoundedDegree.lean` defines the bounded degree subalgebra. This subalgebra has a direct sum decomposition into the homogeneous submodules.
* `Symmetric.lean` defines the permutation action on `MvPowerSeries` and the subalgebra consisting of elements invariant under this action. This action also commutes with the homogeneous projections.

---

With the above machinery in place, we start developing the rest of the theory in the `SymmetricFunction` folder. 
* Define the action of permutations on `MvPowerSeries σ R` and the subalgebra invariant under this action.


```text
SymmetricFun/
  AllPartitions.lean
  Finsupp/
    Partition.lean
  GradedAlgebra/
    Comap.lean
  MvPowerSeries/
    Homogeneous.lean
    BoundedDegree.lean
    Symmetric.lean
  SymmetricFunction/
    Basic.lean
    Grading.lean
    Monomial.lean
    Elementary.lean
    Complete.lean
```

- `AllPartitions.lean` and `Finsupp/Partition.lean` connect partitions with exponent vectors,
  including permutation orbits and chosen representatives.
- `GradedAlgebra/Comap.lean` restricts a grading along an injective algebra homomorphism
  whose range is closed under homogeneous projections.
- `MvPowerSeries/` develops general homogeneity, bounded degree, and symmetry.
  `BoundedDegree.lean` proves the internal `ℕ`-grading of bounded-degree series.
- `SymmetricFunction/Basic.lean` defines the bounded-degree symmetric algebra and its
  inclusion into the bounded-degree algebra.
- `SymmetricFunction/Grading.lean` restricts the bounded-degree grading to symmetric
  functions, using the fact that homogeneous projections commute with permutations.
  The internal pieces are defined directly inside the symmetric-function algebra.
  Both gradings work over any commutative semiring and for any variable type.
- The other `SymmetricFunction/` files develop the individual symmetric-function families;
  `Monomial.lean` constructs the monomial basis and its coordinate equivalence directly
   on these internal homogeneous pieces, with `msymmGraded` as the basis vectors.

Future results on specialization and the fundamental theorem will have their own
files as they are developed. The fundamental theorem will use `MvPolynomial ℕ+ R` directly
as the source of the elementary-generator equivalence with the concrete symmetric-function
algebra, for commutative rings and infinite variable types.

**Plan**
1. Construct the ring of symmetric functions (and polynomials) as a subalgebra of the existing `MvPowerSeries σ R` ring in `mathlib`.
    * Define the subalgebra of bounded degree series. If the type `σ` is finite, then this subalgebra is isomorphic to `MvPolynomial σ R`.
    * Define the action of permutations on `MvPowerSeries σ R` and the subalgebra invariant under this action.
2. Construct the monomial symmetric functions. 
    * If `σ` has cardinality $n \in \mathbb{N}$ then $(m_\mu)_{\ell(\mu)\leq n}$ forms a basis for the symmetric polynomials. Hence if `σ` and `τ` have the same finite cardinality then there is a canonical isomorphism between the associated rings of symmetric polynomials.
    * If `σ` is infinite then $(m_\mu)$ forms a basis for symmetric polynomials.
3. Construct the elementary symmetric functions.
    * When writing $e_\lambda$ in terms of the $m_\mu$'s, the transition matrix $M_{\lambda\mu}$ counts 0-1 matrices with row sums equal to $\lambda$ and column sums equal to $\mu$. Equivalently, this counts simple bipartite graphs whose degree sequences are given by $\lambda$ and $\mu$. A necessary and sufficient condition for the existence of such graphs is given by the [Gale-Ryser theorem](https://en.wikipedia.org/wiki/Gale–Ryser_theorem). This can be used to show that $M_{\lambda\mu}$ is unitriangular with respect to a certain ordering on the partition bases.
    * If `σ` has cardinality $n \in \mathbb{N}$ we get a canonical algebra isomorphism with $R[e_1,\ldots,e_n]$.
    * If `σ` is infinite we get a canonical algebra isomorphism with $R[e_1,e_2,\ldots]$.
4. Construct the complete homogeneous symmetric functions.
    * Prove the relation $\sum_{r=0}^n (-1)^r e_r h_{n-r}$.
    * Define an algebra homomorphism via $\omega(e_r) = h_r$. 
    * If `σ` has cardinality $n \in \mathbb{N}$, then the relation implies $\omega(h_r)=e_r$ for all $1 \leq r \leq n$. Hence, we get a canonical isomorphism with $R[h_1,\ldots,h_r]$.
    * If `σ` is infinite, then $\omega(h_r)=e_r$ for all $r \geq 1$. Hence, we get a canonical isomorphism with $R[h_1,h_2,\ldots]$.
5. Construct Schur functions as generating functions of semistandard Young tableaux.
    * When writing $s_\lambda$ in terms of the $m_\mu$'s, the transition matrix $K_{\lambda\mu}$ are the [Kostka numbers](https://en.wikipedia.org/wiki/Kostka_number), which counts SSYTs of shape $\lambda$ and weight $\mu$. This number is positive if and only if $\lambda$ is larger than $\mu$ in the dominance order. $K_{\lambda\mu}$ is unitriangular if one chooses a linear order on partitions that is compatible with dominance.
    * If `σ` has cardinality $n \in \mathbb{N}$, then the unitriangularity of the transition matrix implies that $(s_\lambda)_{\ell(\lambda)\leq n}$ is a basis.
    * If `σ` is infinite, then $(s_\lambda)$ is a basis.
6. Prove the Pieri rules.
7. Derive other expressions for Schur functions: Jacobi-Trudi identity, Weyl character formula. 
8. Define the Hall inner product.
9. Prove positivity of Littlewood--Richardson coefficients, and/or the Littlewood--Richardson rule. Representation theory of $S_n$ and/or $GL_n$ are not implemented in `mathlib`.
10. (Later?) Refactor `MvPowerSeries` so that it is constructed as a [total monoid algebra](https://en.wikipedia.org/wiki/Total_algebra). The monoid in this case is $(M,+)=\big((\mathbb{Z}_{\geq 0})^I,+\big)$ where $I$ represents the index set for the variables. Note: currently the `MvPolynomial` ring *is* implemented using a general monoid algebra construction.
Many properties of multivariate power series rings fit into this generalized setting.
    * A monoid homomorphism $M \to N$ induces an algebra homomorphism $R[[M]]\to R[[N]]$. An example of this in power series (or polynomial) ring setting occurs when one sends some of the variables to zero. 
    * A distributive group action on $M$ lifts to an action on $R[[M]]$. For example, for power series (or polynomials) we have an action of the symmetric group on the variables. The subset consisting of elements that are invariant under the action form a subalgebra by general principles.


