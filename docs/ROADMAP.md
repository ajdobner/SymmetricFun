# Symmetric function implementation roadmap

The first release will construct the graded ring of symmetric functions, identify it with bounded stable symmetric polynomials, equip it with its usual Hopf structure, and prove that its integral form is the free special lambda ring on one generator. The polynomial-backed representation is accepted. The task registry in `tasks.json` supplies prerequisites, module ownership, and completion criteria.

ENV, API, PART, GRADE, and EBASIS are complete. The public algebra API, partition/weighted-exponent equivalence, weighted grading, and exhaustive degree filtration are proved. The homogeneous and full elementary partition bases are proved. BASE is next in the active implementation run; SPEC and COMPLETE are also ready. The stable realization and subsequent Hopf and lambda-ring milestones remain open. This roadmap intentionally separates implementation work from optional publication on an external proving platform.

## Accepted foundation

Use a dedicated `SymmetricFunction R` type with an explicit algebra equivalence to `MvPolynomial ℕ+ R`. Positive generator indices reuse the colleague's prototype and represent `e n` directly. Public functions `e` and `h` take natural-number indices and satisfy `e 0 = h 0 = 1`. Power-sum generators have positive indices. Keep the public type stable if the internal representation later changes.

API selected a non-abbreviation type synonym with explicit instances and a polynomial algebra equivalence after compiling both that approach and a one-field wrapper. Both passed ordinary algebra elaboration and generator extensionality probes. Accepted examples also compile with the public type locally irreducible. Downstream proofs should use the public evaluation, induction, and extensionality API without unfolding the representation; see `docs/handoffs/API.md`.

The ambient ring and Hopf API assume `CommRing R`. Reusable polynomial and grading lemmas may retain `CommSemiring R` when inexpensive; semiring generality must not delay the integral target. Use the zero coefficient ring without introducing a blanket `Nontrivial R` assumption. Add that assumption only to results that require it.

The grading assigns weight `n` to `e n`. Reuse `MvPolynomial.weightedHomogeneousSubmodule` and `weightedGradedAlgebra`. Define a degree filtration from finite sums of homogeneous pieces; degree-at-most pieces are submodules, generally not subalgebras. Reuse `Nat.Partition d` for each homogeneous basis, with a sigma-type adapter for all partitions if needed.

The integral universal property is

\[
\operatorname{Hom}_{\lambda}(\Lambda_{\mathbb Z},A)\simeq A,
\qquad \varphi\mapsto\varphi(e_1),
\]

for every special lambda ring A. Its inverse sends `e n` to the nth exterior-power operation on the chosen element. This must include targets with torsion. It is freeness on one generator, not an initial-object assertion without a chosen element. A general coefficient ring does not carry a lambda structure merely by being a coefficient ring.

## Milestone order

| Milestone | Required tasks | Result |
| --- | --- | --- |
| Environment | ENV | Pinned package, compiler coverage, diagnostic workflow |
| Polynomial foundation | API, PART, GRADE, EBASIS, BASE | Integral polynomial presentation, graded elementary basis, coefficient functoriality |
| Stable realization | SPEC, FINITE, STABLE | Equivalence to uniformly bounded compatible symmetric polynomial families |
| Classical algebra | COMPLETE, OMEGA, HBASIS, NEWTON | Complete generators, involution, complete basis, integral Newton identities |
| Hopf algebra | HOPF | Standard Mathlib Hopf instance, grading, counit, antipode, base change |
| Lambda infrastructure | LPOLY, LDEFS, LLINE, LSPECIAL | Integral universal polynomials and special lambda structures on finite integer polynomial rings |
| Universal lambda ring | LSTABLE, LFREE | Stable integral operations and the free-object theorem |
| Initial release | RELEASE | All preceding milestones integrated and statement-audited |
| Research APIs | PLETH, RATIONAL, MONOMIAL, SERIES, SCHUR, COMPLETION | Further bases, plethysm, multiple alphabets, symmetric series |

These are proof dependencies, not estimates of equal effort. LPOLY and LSPECIAL are likely the largest mathematical risks. ENV, API, and FINITE expose the most important Lean engineering risks early.

After ENV, PART and a small LPOLY feasibility study can proceed independently of API. The full LPOLY task reuses FINITE's bounds and therefore waits for FINITE. After API, GRADE, SPEC, and BASE have separate files; COMPLETE becomes ready after GRADE. Hopf work need not wait for the full stable realization. LSTABLE needs both the stable realization and finite special lambda operations. Run independent work concurrently only when assigned workers have separate file ownership and shared interfaces have been integrated.

## Polynomial and stable realization proofs

Establish a universal evaluation map from the elementary generators to any commutative R-algebra and an extensionality theorem for algebra maps. These should be the standard entry points for constructing maps throughout the project.

For each N, construct

\[
\rho_N:\Lambda_R\to R[x_1,\ldots,x_N]^{S_N},
\qquad e_n\mapsto e_n(x_1,\ldots,x_N).
\]

Use `MvPolynomial.symmetricSubalgebra`, `esymmAlgHom`, and `esymmAlgEquiv`. Prove the zero-last-variable transition is an algebra map on the symmetric subalgebras, commutes with rho, and behaves correctly for N = 0. Arbitrary finite alphabets can be handled through equivalences with `Fin N` once the core maps are proved.

FINITE is the first substantial proof prototype. Upgrade the finite fundamental theorem to preserve weighted degree in elementary generators. Decompose a preimage into weighted homogeneous pieces and use injectivity plus homogeneous decomposition to eliminate the wrong degrees. This avoids division and works over arbitrary commutative rings. Prove the kernel of rho_N is the ideal generated by elementary generators with index greater than N.

The stable-range theorem says that for N ≥ d, rho_N restricts to an R-linear equivalence on degree-at-most-d pieces. Obtain equality tests in a sufficiently large alphabet, with explicit degree bounds for both sides. This is not a claim that a single rho_N is injective on all symmetric functions.

Define bounded compatible families as symmetric polynomials f_N, compatible under zero-last-variable evaluation, together with the proposition `∃ d, ∀ N, totalDegree f_N ≤ d`. Use a subtype or proof-irrelevant bound, not a chosen bound as mathematical data. Prove an algebra equivalence from the public polynomial-backed type to this ring. To lift a family, choose any stable N ≥ d and show the lift is independent of the choice using the stable-range theorem.

Do not identify the unrestricted inverse limit with the ordinary symmetric-function ring or automatically with its degree completion. These are distinct constructions.

## Classical algebra and Hopf proofs

Define h recursively by E(-u)H(u) = 1. Coefficient identities are finite sums and can be established before introducing any completed ring. Prove h_n is homogeneous of degree n and that specializing gives Mathlib's `hsymm`. Define positive power sums through integral Newton identities and prove specialization to `psum`.

Define omega by `e n ↦ h n`, prove `omega (h n) = e n`, and package the involution as an algebra equivalence. Transport the elementary basis to the complete basis. This avoids proving a second freeness theorem from scratch.

Use algebra-map constructors for

\[
\Delta(e_n)=\sum_{i+j=n}e_i\otimes e_j,\qquad
\varepsilon(e_n)=0\ (n>0),\qquad S(e_n)=(-1)^n h_n.
\]

Check coassociativity and counit laws on generators using tensor associators and finite antidiagonal sums. Since the algebra is commutative, the proposed antipode extends as an algebra map. The convolution compositions in the antipode axioms are algebra maps here; reduce their equality to generators and use the e/h recurrence. Package these maps through the constructors available in the pinned `Bialgebra` and `HopfAlgebra` APIs.

Prove cocommutativity, connected grading, and compatibility with coefficient maps. Derive the complete-function coproduct and primitive positive power sums after NEWTON. Prove the tensor-product interpretation of adding alphabets once the relevant specialization maps are available. Do not use a generic polynomial Hopf structure that declares every elementary generator primitive.

## Integral lambda proofs

Define universal polynomials independently of the eventual lambda structure on symmetric functions. For multiplication, express e_n of the pairwise products x_i y_j in the elementary functions in each alphabet. For iteration, express e_n of the squarefree degree-m monomials in the elementary functions of the original alphabet. Prove stability in alphabet size, sufficient-variable bounds, and weighted degree statements. Fix integer coefficient polynomials with specified variable orderings before defining the classes.

Define pre-lambda structure by lambda_0(a) = 1, lambda_1(a) = a, and the addition convolution law. Define special structure using lambda_t(1) = 1+t and the universal multiplication and iteration identities. Handle index-zero cases explicitly rather than asking a generic positive-index formula to cover them silently. Define preserving ring morphisms and their identity/composition/extensionality API.

For a finite integer polynomial f = sum_m a_m m, construct

\[
\lambda_u(f)=\prod_{m\in\operatorname{support}(f)}(1+mu)^{a_m}.
\]

The factors are units in a one-variable formal power-series ring. Negative coefficients use inverse powers of these units. Prove addition, naturality under monomial substitutions (including setting variables to zero), permutation invariance, and the bound deg(lambda_k(f)) ≤ k d whenever deg(f) ≤ d.

Do not mark this construction special after proving only the addition law. LSPECIAL must prove both universal identities for arbitrary integer coefficients. Start with finite sums of line elements, then prove extension to virtual differences using formal-series identities or a precise polynomial-identity argument. Alternatively, develop a torsion-free criterion after the lambda operations are constructed and prove it completely; do not assume Adams operations characterize structures over arbitrary torsion rings. Record the chosen route and its missing lemmas before a long proof search.

Transport the finite operations through bounded compatible families to Lambda_Z and prove lambda_n(e_1) = e_n. Use the special identities to show that the unique ring map `e n ↦ lambda_n(a)` preserves operations on arbitrary polynomial expressions. Uniqueness then follows from generation. Package the bijection with its evaluation laws and naturality in A.

Only after this construction define integral plethysm through the universal evaluator. Derive associativity and Adams identities; prove compatibility of the lambda and Hopf interpretations of alphabet addition. Tensor-product lambda structures need their own proof if used in this compatibility theorem.

## Research extension contracts

- MONOMIAL: lift finite monomial symmetric polynomials, prove the partition-indexed basis and coefficient extraction. Adapt the colleague's exponent-orbit proof where useful; do not require the entire power-series library.
- RATIONAL: prove polynomial generation and the power-sum basis over a Q-algebra. Define evaluation by a specified family of power-sum images, matching the paper. Distinguish fixed outer coefficients from Adams action on parameters inside an alphabet. Examples include p_k[-X] = -p_k[X] and p_k[tX] = t^k p_k[X].
- SERIES: construct a second realization as bounded symmetric elements of `MvPowerSeries ℕ R`. Port suitable colleague lemmas and prove an algebra equivalence, compatible with elementary, complete, and monomial functions.
- SCHUR: add Jacobi–Trudi, the Schur basis, omega and conjugation, then Hall pairing, skewing and Cauchy identities. Define h_k = 0 for negative determinant indices through an explicit integer-index extension; never use truncated natural subtraction as a substitute.
- COMPLETION: define the degree completion as the product of homogeneous components, with convolution multiplication, and identify its symmetric-series realization. Support Omega = sum h_n and prove precise continuity/substitution hypotheses. Include completed tensor products when extending the coproduct. General infinite plethysm is not automatically defined.
- Multi-alphabet work uses tensor products and explicit alphabet inclusions; separately symmetric functions in several alphabets are distinct from diagonal invariants sometimes also called multisymmetric functions. Mixed polynomial/symmetric objects must support the paper's R[x_1,...,x_r] tensor Lambda_R.

## Review and release criteria

Each task gets an elaborated formal contract before its main proof effort. Review mathematical meaning separately from compiler acceptance. Important checks include the uniform degree quantifier, stable range, tensor base ring, positive power-sum indices, exterior versus symmetric lambda convention, and freeness for torsion targets.

The initial release needs all core tasks, a clean build of every accepted module, no project proof holes or new axioms, and small convention examples. Examples should include degree zero, the empty alphabet, h_2 = e_1^2 - e_2, p_2 = e_1^2 - 2 e_2, the coproduct of e_2, S(e_2) = h_2, and lambda_n(e_1) = e_n. A torsion-valued evaluation example must use a proved lambda-ring instance; do not assume an arbitrary finite ring admits the needed structure.

Use small upstreamable units: finite specialization lemmas, weighted bases, partition adapters, general lambda definitions, and then symmetric-function structures. Preserve attribution. Agree on Mathlib naming and placement before large upstream submissions, without making that discussion a prerequisite for local proof progress.

The mathematical references are the local flagged LLT paper, especially its symmetric-function and plethystic-evaluation sections, and Macdonald's symmetric-function conventions. Existing Mathlib source anchors are `RingTheory/MvPolynomial/Symmetric`, `RingTheory/MvPolynomial/WeightedHomogeneous`, and `RingTheory/HopfAlgebra`. Check their exact declarations against ENV's pin, rather than assuming the inspected local checkout matches the future project.
