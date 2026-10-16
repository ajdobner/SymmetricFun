# Classical Hall pairing and Hopf adjunction

- Owner Codex (single worker); status done.
- Prerequisites MONOMIAL, HBASIS, HOPF complete; source base bd2378f.
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 unchanged.
- Assigned modules Hall/Basic.lean and Hall/Hopf.lean; helper scopes recorded as needed.
- Reuse: pinned Mathlib Basis.constr, dualBasis, PerfectPairing and BilinForm.tensorDistrib.
  No colleague implementation copied; reference checkouts unchanged.

## Proposed declarations and mathematical review before proof search

All statements quantify over arbitrary CommRing R, including zero and torsion rings.
`hall : SymmetricFunction R →ₗ[R] SymmetricFunction R →ₗ[R] R` is the unique
bilinear map taking hBasisAll μ to mBasisAll.coord μ. Thus
`hall (hPart μ.2) (mPart ν.2) = if μ=ν then 1 else 0` for sigma partitions.
A left h-basis expansion is finite; no infinite sum is used in this definition.

`hall_eq_zero_of_degrees_ne hf hg hde` pairs homogeneous degrees d≠e to zero.
`hall_left_nondegenerate` and `hall_right_nondegenerate` assert that a vector
pairing to zero with every bounded vector is zero. `hallHomogeneous d` is the
restriction to the degree-d submodule. `hallHomogeneousPerfect d` is a linear
equivalence from this submodule to its dual, with application equal to hall;
prove a Mathlib IsPerfPair instance, including bijectivity in both arguments.
There is no equivalence to the algebraic dual of the infinite direct sum.

`hall_symm f g : hall f g = hall g f` is a separate substantive obligation:
the complete/monomial normalization alone does not imply symmetry of an
arbitrary pair of bases. The finite complete transition counts nonnegative
integer matrices and transpose exchanges the margins.

`tensorHall` is the product bilinear form, satisfying
`tensorHall (f⊗g) (u⊗v) = hall f u * hall g v`.
`hall_mul f g h : hall (f*g) h = tensorHall (f⊗g) (comultiplication h)`
must use the existing coproduct; prove finite-alphabet coefficient splitting
and actual monomial-orbit coproduct coefficients. No alternate coproduct.

These statements preserve the classical normalization, finite weighted degrees,
and arbitrary-ring generality. Schur orthonormality belongs to HALL-SCHUR and
is not being inferred merely from existence of a Schur basis.

## Validation and remaining work

All parent HALL-CORE acceptance criteria pass. The exact exported interfaces
are printed in scripts/ReviewSchur.lean and indexed in docs/declarations.tsv.
Additional assigned helper modules: Hall/FiniteCoefficient.lean, Hall/Symmetry.lean,
Finite/CompleteCoefficients.lean and Examples/Hall.lean.

Separate statement review (Codex, after proofs, by reading the printed definitions
and types): hall really is complete/monomial duality; finite coefficient extraction
uses actual alphabetSpecialization, and hall_mul uses the existing comultiplication.
The matrix count specifies both margins and transposition swaps them; no orbit
multiplicity or integer is inverted. Nondegeneracy is in both arguments. The
perfect equivalence and IsPerfPair instance are restricted to homogeneousSubmodule R d,
including d=0 and the zero ring. All coefficient hypotheses are CommRing alone.
The tensor form is explicitly the product on pure tensors, not an infinite dual.
Schur orthonormality is not inferred and remains HALL-SCHUR.

Checks (all exit 0):
- python3 scripts/check_project.py: 110 accepted modules; 1,970 transitive axiom
  audits, only propext/Classical.choice/Quot.sound; notation/lambda regressions pass.
- python3 scripts/test_check_project.py: all five checker guards pass.
- lake env lean scripts/ReviewSchur.lean: definitions/types and key axioms inspected.
- lake env lean scripts/DeclarationIndex.lean: 1,421 noninternal declarations.
- Lean MCP Examples/Hall.lean: no diagnostics; git diff --check passes.
- Examples cover empty partitions, repeated (2,2) with ZMod 6 coefficients,
  one-row duality, finite one-variable coefficients, distinct degrees, the actual
  Hopf adjunction, and the perfect equivalence over PUnit.

Logs: /tmp/hall-core-check.log and /tmp/hall-core-review.log.
No dependencies or reference checkouts changed. No outstanding HALL-CORE obligations.

Proof engineering note: nested Basis.ext with LinearMap.mul compositions triggered
large definitional reductions; the final hall_mul uses the finite complete-basis
expansions instead, at the default heartbeat limit. No option override remains.

Exact checked Lean source SHA-256:

- `Hall/Basic.lean`: `9cebc9ccb9694bcd38c6be2cc75a0f8b6585dfcebe4806d8b9133c5f7a1bed4c`
- `Hall/FiniteCoefficient.lean`: `647ce6cadd3c7d8dfd893c03e12ba754b25a1d8299d000dea91e9133c62fc1f7`
- `Hall/Hopf.lean`: `8861364f9813e8d787dbded69c8b646672046b559ef6620b09a3e7917a29baa6`
- `Hall/Symmetry.lean`: `94464c139dc46223ec4c5468257c7261e8714b7e67756a426ae16c710ce3c2f0`
- `Finite/CompleteCoefficients.lean`: `3dfdb4a531585df0f4436c59ec0f4a3b2a1ea6135bb5c0387632ba285be3f088`
- `Examples/Hall.lean`: `bc736f8ca5f2cc61941acc7c12f17e232b8f22260dde51a38c87a8d18094687d`
