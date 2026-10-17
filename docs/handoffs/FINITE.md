# Weighted finite fundamental theorem and stable range

- Task: FINITE; owner: Codex (single worker); status: done.
- Prerequisites: GRADE fc48b62, SPEC 5f7f1c1; base checkpoint 3dae479.
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- Scope: SymmetricFunctions/Finite/Weighted.lean and Finite/StableRange.lean.
  Shared graded evaluation helpers may be extended with explicit documentation.
- References: pinned finite fundamental theorem, weighted homogeneous
  decomposition, polynomial ideals and degree bounds. No colleague code copied.

## Mathematical contract and proposed interface

For every CommRing R and N, the finite elementary presentation
`MvPolynomial.esymmAlgEquiv (Fin N) R (Fintype.card_fin N)` converts weighted
homogeneous degree d (weight i = i.val+1) exactly to ordinary homogeneous degree d.
Its inverse must preserve this degree, not just its forward map.

Construct `finiteLift R N` from finite elementary-generator polynomials to the
public symmetric-function algebra. Compose with the inverse finite presentation
to lift every symmetric polynomial. Prove rho_N is surjective and
`RingHom.ker (rho R N).toRingHom = Ideal.span {e k | k > N}`.
For N ≥ d, restrict rho_N to an R-linear equivalence from degreeLE R d to the
submodule of symmetric N-variable polynomials of totalDegree ≤ d. Prove a bounded
equality test with explicit bounds on both inputs.

## Pre-proof statement review

The polynomial generators in the finite presentation have weights 1 through N;
ordinary total degree is used only after specialization to alphabet variables.
The kernel includes all and only consequences of e k=0 for k>N. In degree at
most d and N≥d none of those high generators can occur. There is no claim of
global injectivity of rho_N. The zero polynomial and N=d=0 are included, without
Nontrivial, flatness, field, or characteristic-zero assumptions.

## Strategy

First prove weighted evaluation commutes with homogeneous projections, then use
finite-presentation injectivity to reflect homogeneity. Lift symmetric polynomials
via its inverse. Prove the kernel using the quotient map by the high-generator
ideal and public generator extensionality. Prove the degree-bounded inverse laws
from weighted support bounds and finite homogeneous reconstruction.
Final declarations, separate statement review, validation and remaining goals
will be recorded as implementation progresses.

## Final interface and statement-only review

Supporting exports in `SymmetricFunctions`: `weightedComponent_aeval`,
`weightedHomogeneous_aeval_iff`, `isHomogeneous_esymm`.
The first two work for arbitrary additive commutative weight monoids over any
commutative semiring. They use OMEGA's independent Grading/Evaluation helper;
the task registry now records that additional completed prerequisite.

Exports in `SymmetricFunction` from Weighted: `finitePresentation`,
`finitePresentation_apply`, `finitePresentation_homogeneous_iff`,
`finitePresentation_symm_homogeneous`, `finiteLift`, `finiteLift_X`,
`rho_comp_finiteLift`, `liftSymmetric`, `rho_liftSymmetric`, `rho_surjective`,
`isHomogeneous_finiteLift`, `isHomogeneous_liftSymmetric`, `isHomogeneous_rho`,
`symmetricComponent`, `coe_symmetricComponent`,
`isHomogeneous_symmetricComponent`, and `sum_symmetricComponent`.

Exports from StableRange: `truncate`, `truncate_e_of_le`, `truncate_e_of_lt`,
`truncate_e`, `highElementaryIdeal`, `highElementaryIdeal_le_ker`,
`quotient_comp_truncate`, `ker_rho`, `truncate_of_homogeneous`,
`truncate_of_mem_degreeLE`, `finiteDegreeLE`, `mem_finiteDegreeLE`,
`rho_mem_finiteDegreeLE`, `liftSymmetric_mem_degreeLE`, `stableRangeEquiv`,
`stableRangeEquiv_apply`, `stableRangeEquiv_symm_apply`,
`rho_eq_iff_of_degreeLE`, and `rho_eq_iff_of_bounds`.

The implementing worker separately inspected the fully elaborated types using
`#check @...`. The finite algebra equivalence is exactly Mathlib's elementary
presentation; input weight is i.val+1 and output homogeneity is ordinary alphabet
degree. Both directions are proved. `highElementaryIdeal` is the ideal span of
`e '' {k : ℕ | N < k}`. `finiteDegreeLE` is the inverse image of Mathlib's
restrictTotalDegree under the symmetric-subalgebra inclusion, with a proved
membership equivalence to totalDegree ≤ d. `stableRangeEquiv R N d hd` is an
R-linear equivalence with hd : d ≤ N and forward map rho_N. The inverse is the
canonical finite lift, whose degree bound is proved independently of N ≥ d.
The two-input equality test has an explicit bound for each input. All these
results use arbitrary CommRing R, without nontriviality, flatness, characteristic
or torsion assumptions. No mathematical contract was weakened.

## Validation and completion

- Lean MCP searches and final diagnostics: clean for both finite modules.
- `lake env lean .scratch/FiniteReview.lean`: exit 0; statement-only review.
- `python3 scripts/check_project.py`: exit 0; all 15 accepted modules built cleanly,
  all 360 declarations passed the transitive axiom audit.
- `python3 scripts/test_check_project.py`: all five tests passed.
- `git diff --check`: passed; both modules in root coverage.
- Examples cover the N=d=0 equality test and the kernel generator e (N+1),
  with the public type locally irreducible.

All FINITE acceptance criteria pass. Stable specialization is not globally
injective: the kernel contains every elementary generator above N.
STABLE is selected next; NEWTON and LPOLY are also ready. RELEASE remains open.

## Proof implementation details

Projection compatibility is proved by ordinary monomial/addition induction,
using weighted homogeneity of each substituted monomial. This avoids managing
infinite-index finite sums. The kernel proof compares quotient algebra maps on
generators, not coefficients. The degree-bounded inverse uses symmetric
homogeneous components and their finite reconstruction. Mathlib killCompl was
inspected; it was unnecessary for this public quotient/extensionality proof.

Checked source SHA-256:
- Weighted.lean: `03dbc60e23fa3e6d0500a81a42a6a3764ef2b69966cad9273e27c28015a68148`.
- StableRange.lean: `0d90e302dc19241c9cede8480dcab6ea4d388b97c39f23bd8fc4be8b7f42c3cb`.
