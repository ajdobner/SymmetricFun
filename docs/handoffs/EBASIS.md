# Elementary partition bases

- Task: EBASIS; owner: Codex (single worker); status: done.
- Prerequisites: PART at c62ade0; GRADE at fc48b62.
- Pin: Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- Scope: `SymmetricFunctions/Basis/Elementary.lean`, root import and documentation.
- Reuse audit consulted. The colleague's upstream Basic.lean proposed a weighted
  monomial basis and unfinished elementary partition basis at commit
  98938de95a12b3ed363653cb980588e2a9188cb8. Reconstruct using pinned Mathlib's
  `basisRestrictSupport`, rather than copying colleague proof code; preserve this
  attribution. No inherited draft imports or license changes.

## Mathematical contract and formal interface

Over arbitrary commutative semirings, the degree-d piece has a basis indexed by
Mathlib `Nat.Partition d`, with vector the product of elementary functions over
its parts. The full ring has a basis indexed by `Σ d, Nat.Partition d`, obtained
from the direct sum of these homogeneous bases. Coefficients are polynomial
coefficients at the partition's multiplicity vector. Multiplication concatenates
part multisets; empty products are one.

Confirmed declarations in `SymmetricFunction`:

```lean
ePart (μ : Nat.Partition d) : SymmetricFunction R
polynomialEquiv_ePart (μ : Nat.Partition d) :
  polynomialEquiv R (ePart μ) = MvPolynomial.monomial (Partition.toExponents μ) 1
isHomogeneous_ePart (μ : Nat.Partition d) : IsHomogeneous (ePart (R := R) μ) d
eBasis (R) (d : ℕ) : Module.Basis (Nat.Partition d) R (homogeneousSubmodule R d)
eBasis_apply (μ : Nat.Partition d) : (eBasis R d μ : SymmetricFunction R) = ePart μ
eBasis_repr (f : homogeneousSubmodule R d) (μ : Nat.Partition d) :
  (eBasis R d).repr f μ = (polynomialEquiv R f).coeff (Partition.toExponents μ)
eBasisAll (R) : Module.Basis (Σ d, Nat.Partition d) R (SymmetricFunction R)
eBasisAll_apply (μ : Σ d, Nat.Partition d) : eBasisAll R μ = ePart μ.2
```

Also construct a general weighted monomial basis with a monomial-value and
coefficient formula, and partition-union/product lemmas.

## Pre-proof statement review

The implementing worker checked that multiplicities, not weighted counts,
index polynomial monomials. Partition size is the weighted degree, so degree-d
basis membership uses PART's exact equality. The full basis is a direct sum,
not a product; all expansions remain finite. Coefficients and all basis
constructions must permit the zero ring, without a hidden nontriviality or
field assumption. The empty partition is the degree-zero vector one. No
contract revision is needed.

## Strategy and validation

Transport `MvPolynomial.basisRestrictSupport` along the equality with the
weighted homogeneous submodule, then along the public polynomial equivalence.
Reindex by `Partition.weightedExponentEquiv`. Use `DFinsupp.basis` and GRADE's
`decompose` equivalence for the full basis. The construction and validation are complete.

## Final statement review

A separate statement-only review by the implementing worker checked the fully
elaborated `weightedMonomialBasis`, `eBasis`, `eBasisAll`, their value and
coefficient formulas, and `ePart_mul`. All coefficient assumptions remain
`CommSemiring R`; arbitrary commutative rings, including the zero ring, are
included. The general weight monoid is any additive commutative monoid. The
full basis is actually constructed through `DFinsupp.basis` and `decompose`,
with index `Σ d, Nat.Partition d`. Its coefficient formula agrees with the
homogeneous formula because the partition's monomial has exactly that degree.
No conclusion is included among the hypotheses, and no contract was changed.

## Exported declarations and implementation notes

`SymmetricFunctions`: `weightedMonomialBasis`, `weightedMonomialBasis_apply`,
`weightedMonomialBasis_repr`.

`SymmetricFunctions.Partition`: `union`, `union_parts`, `toExponents_union`.

`SymmetricFunction`: `ePart`, `ePart_eq_prod`, `polynomialEquiv_ePart`,
`isHomogeneous_ePart`, `ePart_zero`, `ePart_mul`, `homogeneousPolynomialEquiv`,
`homogeneousPolynomialEquiv_apply`, `homogeneousPolynomialEquiv_symm_apply`,
`eBasis`, `eBasis_apply`, `eBasis_repr`, `eBasisAll`, `eBasisAll_repr`,
`eBasisAll_apply`.

The full coefficient formula is
`(eBasisAll R).repr f μ = (polynomialEquiv R f).coeff (Partition.toExponents μ.2)`.
The basis structures provide finite expansions and linear independence, not
just spanning families. Standard `Module.Basis.sum_repr` supplies reconstruction.

Useful elaboration detail: declare the coercion lemmas for
`homogeneousPolynomialEquiv` explicitly. Simplifying its full implementation
leaves submodule coercions stuck under this pin's implicit transparency.
For the general basis value, reducing to `Finsupp.supportedEquivFinsupp_symm_single`
is shorter than unfolding the whole basis structure.

## Validation and completion

- `python3 scripts/check_project.py`: final exit 0; all seven accepted modules
  built without warnings; transitive axioms of 166 declarations audited with
  only the allowed three Lean foundations.
- Lean MCP declaration searches and final diagnostics passed without warnings.
- `lake env lean .scratch/EBasisReview.lean`: exit 0; fully quantified signatures
  inspected separately from proof scripts.
- Examples check the empty partition vector, the single part of size two, and
  multiplication of full-basis vectors by partition union. They mark the public
  symmetric-function type locally irreducible.
- `git diff --check`: passed; root import coverage includes the new module.
- Checked source SHA-256 for `SymmetricFunctions/Basis/Elementary.lean`:
  `c50d907627d0b4f8981c8f76e225d2c3a75c16de0564469de5c729e0d4b6a59f`.
  Base checkpoint: `fc48b62`.

All EBASIS acceptance criteria passed, with no remaining EBASIS obligations.
Continue the active goal with BASE, then SPEC. COMPLETE is also independently
ready. RELEASE, stable realization, Hopf, and lambda milestones remain open.
