# Integral complete symmetric functions

- Task: COMPLETE; owner: Codex (single worker); status: done.
- Prerequisites API c62ade0 and GRADE fc48b62; base checkpoint 5f7f1c1.
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- Scope: SymmetricFunctions/Complete.lean, root and task documentation.
- Sources: Mathlib finite antidiagonal sums and existing public grading API.
  No colleague code copied.

## Mathematical contract and proposed interface

For every commutative ring R, recursively define h 0 = 1 and
h (n+1) = ∑ (i,j) in antidiagonal n, (-1 : R)^i • (e (i+1) * h j).
All recursive calls have j ≤ n. Prove h n homogeneous of weighted degree n.
Prove the coefficient identities E(-u)H(u)=H(u)E(-u)=1 as finite antidiagonal
sums, and the sign-reversed versions needed by the antipode. Export recurrence
and uniqueness statements so omega can be proved without changing the definition.

## Pre-proof statement review

The scalar sign is integral, no division or inversion of an integer occurs.
Coefficients are arbitrary commutative rings including the zero ring. The index
zero is the unit. Antidiagonal sums enforce total degree n; the recursion defines
a finite polynomial for every n. No completed symmetric-function type is used.
Homogeneity is weighted degree from GRADE, not ordinary generator degree.
No contract revision is needed. Final elaborated statement review passed.

## Strategy

Use well-founded recursion with the second antidiagonal coordinate decreasing.
Extract the endpoint in a successor antidiagonal to prove convolution. Use
antidiagonal swapping and scalar signs for the other orders. Prove homogeneity
and uniqueness by strong induction. Validation and exact exports are recorded below.

## Formal interface and separate statement review

Exports in `SymmetricFunction`: `h`, `h_zero`, `h_succ`, `h_one`, `h_two`,
`isHomogeneous_h`, `e_h_convolution`, `h_e_convolution`,
`e_h_convolution_signed`, `h_e_convolution_signed`, `e_succ_h`, and `h_unique`.
The generated well-founded recursion auxiliaries are also audited.

The implementing worker separately inspected all elaborated main types with
`#check @...`. Each has only CommRing R, without torsion, characteristic or
nontriviality assumptions. The convolution RHS is 1 at n=0 and 0 otherwise.
Both multiplication orders, and the two placements of the scalar sign, are
proved. `e_succ_h` is the dual finite recurrence expressing e through h;
`h_unique` proves uniqueness from the initial value and original recurrence.
Examples check h 2 + e 2 = e 1 squared and degree at most 3 for h 3.
No statement assumes an inverse series or desired morphism exists.

## Validation, checked source, and completion

- Lean MCP final diagnostics: clean, no errors or warnings.
- `lake env lean .scratch/CompleteReview.lean`: exit 0; types reviewed separately.
- `python3 scripts/check_project.py`: exit 0; all 10 accepted modules built cleanly,
  transitive axioms of all 243 declarations passed (only allowed foundations).
- `git diff --check`: passed; Complete is in root import coverage.
- SHA-256 Complete.lean:
  `13de6bd9c14f90073dd5241377e19832cfad3937ee1da9b33c661b9f76e8b1b7`.
- All COMPLETE acceptance criteria pass, with no remaining COMPLETE obligations.

Implementation detail: ordinary finite-sum binders do not retain membership in
recursive-call termination goals. Use the attached antidiagonal in the definition,
then expose the ordinary sum through `Finset.sum_attach` with an explicit function.
No completed ring or power-series dependency was introduced.

OMEGA is selected next; NEWTON and FINITE are also ready. RELEASE remains open.
