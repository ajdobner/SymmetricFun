# Complete partition bases and polynomial freeness

- Task: HBASIS; owner: Codex (single worker); status: done.
- Prerequisites: OMEGA ce87705, EBASIS e20719b.
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- Scope: SymmetricFunctions/Basis/Complete.lean, root/docs.
- Sources: public omega and elementary bases, Mathlib Basis.map.
  No colleague code copied.

## Mathematical contract and proposed declarations

For every commutative ring R, define hPart μ as the product of h over the parts
of Mathlib's Nat.Partition d. Prove omega(ePart μ)=hPart μ and the inverse.
Transport the homogeneous basis by omegaHomogeneous and the all-partitions
basis by omega. Prove the value and coordinate formulas: complete coordinates
of f are elementary coordinates of omega f. Construct the polynomial algebra
equivalence `completePolynomialEquiv : SymmetricFunction R ≃ₐ[R] MvPolynomial ℕ+ R`
by applying omega then polynomialEquiv. It sends h i to X i for every positive i.
Supply unique evaluation on positive h generators into arbitrary commutative
R-algebras, and basis product evaluation formulas.

## Pre-proof statement review

The full basis is indexed by a sigma of Nat.Partition d and consists of finite
expansions. Index zero h 0 = 1 is not a free variable. Coordinate extraction
must apply omega first, not reuse elementary coordinates unchanged. Polynomial
freeness is an algebra equivalence and unique evaluation, not only spanning.
No Nontrivial or torsion-free hypotheses. No contract changes needed.

## Strategy and obligations

Transport already proved basis and polynomial structures. Final elaborated
statement review, examples, integration, and axiom audit passed.

## Exported declarations and separate statement review

Exports in `SymmetricFunction`: `hPart`, `hPart_eq_prod`, `omega_ePart`,
`omega_hPart`, `isHomogeneous_hPart`, `hPart_zero`, `hPart_mul`, `hBasis`,
`hBasis_apply`, `hBasis_repr`, `hBasisAll`, `hBasisAll_apply`, `hBasisAll_repr`,
`completePolynomialEquiv`, `completePolynomialEquiv_h`,
`completePolynomialEquiv_symm_X`, `algHom_ext_h`, `completeEval`,
`completeEval_h`, `completeEval_h_zero`, `completeEval_unique`,
`completeEvalEquiv`, `completeEval_hPart`, and `completeEval_hBasisAll`.

The implementing worker separately inspected the elaborated main declarations
with `#check @...`. Every basis and presentation works over arbitrary CommRing R.
The target of evaluation can be any commutative R-algebra; no characteristic,
nontriviality, or torsion-free assumption occurs. Index zero is one, positive
indices are polynomial variables, and full basis coordinates are finitely
supported. Both coordinate formulas correctly use polynomial coefficients after
omega. No mathematical contract changes were required.

## Validation and completion

- Lean MCP final diagnostics: no errors or warnings.
- `lake env lean .scratch/HBasisReview.lean`: exit 0; statement-only review.
- `python3 scripts/check_project.py`: exit 0; all 13 accepted modules built cleanly;
  all 305 accepted declarations passed the transitive axiom audit.
- Examples cover the empty partition, the degree-two single-part vector, and
  evaluation of h 1 squared; public type locally irreducible.
- `git diff --check`: passed; root import includes Basis.Complete.
- Source SHA-256:
  `5fe3bec7a2fccd710bb1d5a334fa8081a7316fb656183606e8adbdf9030108f1`.

All HBASIS acceptance criteria passed, with no remaining HBASIS obligations.
FINITE is selected next; NEWTON is independently ready. RELEASE remains open.
