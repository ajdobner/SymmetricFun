# Stable integral universal lambda polynomials

- Task: LPOLY; owner: Codex (single worker); status: done.
- Prerequisites: FINITE ac261f7 and STABLE e257846 (added explicitly for the
  already-proved bounded stable lift; no lambda dependency).
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- Scope: LambdaRing/UniversalPolynomials.lean and supporting modules.
- References: pinned finite elementary presentation and symmetric polynomials,
  Finset.powersetCard and permutation APIs. No colleague code copied.

## Mathematical contract and proposed interface

All universal polynomials have integer coefficients and fixed positive-index
variables. The product polynomial P_n has variables ℕ+ ⊕ ℕ+ (left then right),
and the iteration polynomial Q_(n,m) has variables ℕ+. These are ordinary finite
MvPolynomial values, not formal infinite sums. Their support is bounded:
P_n has weight (n,n), so uses only e_1,...,e_n in each block; Q_(n,m) has
weight n*m, so uses only e_1,...,e_(n*m). A countable ambient index set makes
substitution into arbitrary lambda targets uniform without changing finiteness.

For every two finite alphabets of sizes N,M, substituting elementary polynomials
into P_n gives e_n of all pairwise products x_i*y_j. For every alphabet of size N,
substituting into Q_(n,m) gives e_n of the squarefree degree-m monomials in x.
Prove uniqueness with the given weight/support bounds, sufficient variable
bounds N,M >= n (product) and N >= n*m (iteration), and independence under
zero-variable truncation. The identities then hold for smaller alphabets too.

Boundary conventions: P_0=1, P_1=X_left,1*X_right,1;
Q_(0,m)=1, Q_(1,m)=X_m for m>0, Q_(n,1)=X_n for n>0;
Q_(n,0)=1 for n=0 or n=1 and 0 for n>1. The squarefree degree-zero
alphabet is the singleton monomial 1 even for an empty base alphabet.
No lambda structure is used or assumed in these constructions.

## Pre-proof statement review

The degree of the product polynomial is separately n in the two weighted
blocks, hence total weight 2n. Iteration has weight n*m. These are weighted
elementary-generator degrees, not ordinary polynomial degree in those generators.
The m=0 iteration case is constant and must be handled explicitly; a positive
index X_0 will never be introduced. Elementary specialization to a sufficiently
large alphabet is injective only within the stated bounds. Nothing requires
rational coefficients or cancellation of integers. Integer polynomial identities
will later be substituted into arbitrary special lambda targets, including torsion.

## Planned proof decomposition

1. Generic finite elementary evaluation and its invariance under permutation,
   homogeneous substitution, and adjoining variables that evaluate to zero.
2. Squarefree-monomial alphabets: symmetry, degree n*m, zero-variable stability.
   Lift the bounded compatible family, then prove the support bound and uniqueness.
3. Separately symmetric pair-product alphabets: lift in the two elementary blocks,
   prove bidegree (n,n), stability, uniqueness, and boundary cases.
4. Review elaborated statements separately, audit axioms, run full checker,
   and commit. Each intermediate checkpoint will retain in_progress until all
   product and iteration criteria pass.

No LPOLY declarations are accepted or claimed proved at this initial handoff.

## Finite-variable uniqueness refinement

Before proving uniqueness, strengthen the proposed interface: elementary
specialization at size N is injective for *all* polynomials whose occurring
positive variables have indices at most N. This does not require homogeneity.
The proof uses FINITE's canonical truncate/lift and equality of polynomial
homomorphisms on the variables actually occurring. Universal iteration
uniqueness then uses the proved variable bound n*m, while its separate weighted
homogeneity theorem supplies the sharper mathematical degree information.

## Product substep: reviewed constructive strategy

For the second alphabet use the existing coefficient ring SF Z with elementary
e_k. For each finite first alphabet X, take the coefficient of u^n in
  product_i (sum_k C(e_k) X_i^k u^k).
Each coefficient is an actual finite polynomial. It is symmetric in X,
homogeneous of X-degree n, and compatible with setting the last X-variable to
zero. Its coefficients have Y-weight n. Lift this bounded family using STABLE
over the coefficient ring SF Z; then flatten the iterated polynomial
presentation into variables ℕ+ ⊕ ℕ+. After specializing Y, the displayed factors
become product_j (1 + X_i Y_j u), proving the pair-product interpretation.

To verify bidegree and uniqueness, use the injectivity of elementary substitution
in one block over a polynomial coefficient ring, transported through Mathlib's
`MvPolynomial.sumAlgEquiv`. Apply the existing weighted-substitution reflection
lemma with weights in ℕ×ℕ. This does not require a new representation of SF,
separate symmetric surjectivity infrastructure, or any lambda-ring identity.

## Checkpoint 1: integral iteration polynomials

Implemented and validated:
- Finite.lean: `elementaryOn`, `elementaryValue`, zero/one formulas, ring-map
  naturality, vanishing beyond alphabet cardinality, embedding/permutation
  invariance, zero-extension invariance, `aeval_esymm`, homogeneous degree.
- Squarefree.lean: `SquarefreeIndex`, `squarefreeValue`, induced embeddings and
  their exact range, `iterationValue`, all zero/one cases, `iterationFinite`,
  coefficient-map naturality, symmetry, degree n*m, and zero-last stability.
- Bounds.lean: `elementarySpecialization_eq_rho`, `truncate_of_vars_le`, and
  `elementarySpecialization_injective_of_vars_le` over arbitrary CommRing R.
- Iteration.lean: `iterationFamily`, `iterationFunction`, the canonical lift
  at every N >= n*m, `iterationPolynomial`, weighted degree and variable bounds,
  specialization at all N (also over arbitrary R), evaluation at any finite
  family of elements of any commutative ring, uniqueness at N >= n*m,
  truncation stability, and all zero/one boundary formulas.

The same worker separately reviewed fully elaborated statements in
`.scratch/IterationReview.lean`. The universal polynomial has coefficients Z;
its substitution identity quantifies over every CommRing A, with no
Nontrivial or torsion restriction. Uniqueness permits an arbitrary polynomial
q with variables bounded by n*m; it does not assume q homogeneous or assume a
lambda structure. The m=0 convention is explicitly `if n <= 1 then 1 else 0`.
Kernel-checked examples include the empty alphabet at (n,m)=(1,0), Q_(2,0)=0,
Q_(0,0)=1, and Q_(1,1)=X_1.

Validation: `python3 scripts/check_project.py` passed, building all 30 accepted
modules and auditing 626 declarations. `lake env lean .scratch/IterationReview.lean`
passed with direct axiom checks of evaluation and uniqueness. Lean MCP final
Iteration diagnostics were empty. `git diff --check` passed. The exact checked
source state is the commit containing this checkpoint. The Lake configuration
now declares the LambdaRing library; dependency pins and manifest are unchanged.

Remaining LPOLY work: product polynomials and their bidegree, specialization,
stability, uniqueness, and boundary theorems. LDEFS is not yet ready. No lambda
structure or special identity has been assumed or claimed at this checkpoint.

## Checkpoint 2: stable product construction and bidegree

The auxiliary coefficient ring is `MvPolynomial ℕ+ R` (the public polynomial
presentation of the second symmetric alphabet). This is equivalent to the
reviewed SF R coefficient plan and avoids an unnecessary wrapper conversion;
the foundational SF representation is unchanged.

- Generating.lean: finite `elementarySeries` and its coefficient formula.
- ProductFinite.lean: `elementaryCoefficient`, `productFactor`, `productSeries`,
  finite coefficient formula, symmetry and homogeneous first-alphabet degree,
  zero-last stability, `productFamily`, `productFunction`, and computation by
  a lift at every first-alphabet size N>=n.
- TwoAlphabets.lean: sum/iterated-presentation coefficient and rename formulas,
  `leftElementary`, its injectivity over an arbitrary polynomial coefficient
  ring, and `leftElementary_weighted_iff` for arbitrary additive weight monoids.
- ProductDegree.lean: `firstAlphabetWeight`, `elementaryBlockWeight`,
  `productFinite_bidegree`, `productPresentation`, and its bidegree.
- Product.lean: `productPolynomialOver`, its equality to every stable finite
  presentation, `productPolynomial : ℕ → MvPolynomial (ℕ+ ⊕ ℕ+) ℤ`, bidegree
  `(n,n)`, and separate bounds `productPolynomial_vars_left_le/right_le`.

Validation: `python3 scripts/check_project.py` passed for all 35 accepted modules
and 681 transitive-axiom-audited declarations. Lean MCP final Product diagnostics
were empty. The separate elaborated-type review in `.scratch/ProductDegreeReview.lean`
passed and confirms the full bidegree, coefficient ring, positive indices, and
N>=n bound; direct axiom audit uses standard foundations only. `git diff --check`
passed. Exact checked state: the commit containing this checkpoint.

Remaining LPOLY obligations: prove the pairwise-product evaluation identity,
two-alphabet uniqueness with both variable bounds, explicit truncation and
boundary conventions, and final task validation. The constructed polynomial
is not yet claimed to satisfy all product acceptance criteria. Product-family
proofs use a formal-series coefficient; they do not introduce completed
symmetric functions or a lambda structure.

## Completion: specialization, uniqueness, and stability

- ProductEvaluation.lean: `secondAlphabetEval`, `twoAlphabetEval`, coefficient
  evaluation of the finite generating product, `productPolynomial_eval_fin`,
  and `productPolynomial_eval` for every pair of finite alphabets in every
  commutative ring.
- TwoAlphabetBounds.lean: elementary substitution in the right and both blocks,
  `twoElementary_injective`, `positiveIndexEmbedding`, finite-support adapters,
  and `twoElementary_injective_of_vars_le`. Both blocks have explicit bounds.
- ProductSpec.lean: `pairProductPolynomial`, `productPolynomial_specialize`,
  `productPolynomial_unique`, `productPolynomial_truncate`, zero and one
  formulas, empty-alphabet vanishing, and `pairProductValue_extend_left/right`.
- Finite.lean additionally exports evaluation with a coefficient ring map and
  elementary evaluation under uniform scaling. TwoAlphabets.lean exports
  `aeval_sumAlgEquiv` for evaluating the flattened presentation.

Separate final statement review (Codex, single worker):
`lake env lean .scratch/LPolyFinalReview.lean` prints the fully elaborated
statements, which were read independently of their proofs. Product and iteration
polynomials have coefficients Z. Evaluation permits arbitrary CommRing A and
finite index types, including empty types and the zero ring; there is no
Nontrivial, characteristic-zero, or torsion-free assumption. Product uniqueness
requires N,M >= n and each block's variables <= n. Iteration uniqueness requires
N >= n*m and variables <= n*m. These are support restrictions on an otherwise
arbitrary candidate polynomial, not assumptions of its desired identity.
All indices n,m include zero. Q_(n,0) is exactly 1 for n<=1 and 0 otherwise,
reflecting the singleton squarefree degree-zero monomial. P_0=1 and
P_1=X_left,1*X_right,1. No lambda structure occurs in the construction.

Final validation on the exact source state in the completion commit:
- `python3 scripts/check_project.py`: exit 0; all 38 accepted modules built,
  root coverage checked, 721 declarations transitively axiom-audited.
- `python3 scripts/test_check_project.py`: exit 0; all five tests passed.
- `lake env lean .scratch/LPolyFinalReview.lean`: exit 0; direct audits of both
  evaluation and uniqueness theorems use only propext, Classical.choice, Quot.sound.
- Lean MCP final ProductSpec diagnostics: empty; changed files compiled cleanly.
- `git diff --check`: exit 0.
- Accepted examples cover empty alphabets, Q_(2,0)=0, Q_(0,0)=1,
  and P_1 evaluation in an arbitrary commutative ring.

All LPOLY acceptance criteria pass. LDEFS is now ready. The actual lambda
structures, special identities on virtual differences, and free-object theorem
remain later tasks. Dependency pins and original colleague checkouts are unchanged.
