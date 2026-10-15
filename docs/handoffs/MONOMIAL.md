# Monomial symmetric functions and partition coefficients

- Task MONOMIAL; owner Codex (single worker); status done.
- Prerequisites: PART and STABLE complete (see their handoffs); resumed after
  PLETH 33d7be0 and LSIMP 9aa493d.
- Lean v4.34.1, pinned Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 unchanged.
- Scope: Finite/Monomial, Partition/Orbits, Basis/Monomial, Examples/Monomial.

## Contract and proposed exact interfaces, before proof search

For each CommRing R, natural d and Mathlib partition mu : Nat.Partition d,
construct `mPart mu : SymmetricFunction R` by applying the inverse proved stable
realization to the family `MvPolynomial.msymm (Fin N) R mu`. The pinned Mathlib
already defines this finite orbit sum using distinct multisets of alphabet
variables with multiplicity partition mu; it proves permutation invariance.
We will reuse that definition, not a substitute elementary-basis vector.

Define `exponentParts (a : sigma ->₀ Nat) : Multiset Nat` as the multiset of
nonzero values on a.support. The intended coefficient formula is, for every
N and a : Fin N ->₀ Nat, including small N:
`(rho R N (mPart mu)).val.coeff a = if exponentParts a = mu.parts then 1 else 0`.
Prove exactly the corresponding finite msymm coefficient formula first,
zero-last-variable compatibility, and homogeneity d (hence totalDegree <= d).
The empty partition gives one, repeated parts give coefficient one rather than
an orbit stabilizer factor, and cardinal(mu.parts)>N gives zero specialization.

Construct `mBasis R d : Module.Basis (Nat.Partition d) R
(homogeneousSubmodule R d)` with vector mPart mu. Its coordinates are coefficients
in a stable finite alphabet at an exponent vector with shape mu. Construct the
all-partitions basis through the existing homogeneous direct sum. Coefficient
formulas must identify actual finite polynomial coefficients, not merely
coordinates in a renamed abstract basis.

## Pre-proof statement review

The implementing worker checked that the finite Mathlib msymm uses each
exponent orbit element once. The weight is the sum of variable exponents,
equal to mu.parts.sum=d; repeated parts are retained. Rings may have zero
divisors, additive torsion, or be the zero ring. No factorial division,
characteristic hypothesis or Nontrivial assumption is permitted in basis
constructions. Small alphabets have the explicit zero cases rather than
being silently excluded by a stable-range premise.

## Reuse and strategy

Pinned Mathlib Sym.equivNatSum, Multiset.toFinsupp, Nat.Partition.ofSym and
msymm/rename_msymm are available. Extend their coefficient/transition API.
For orbit classification inspect the colleague's
SymmetricPoly/Finsupp/SymmetricAction.lean at inherited source commit
98938de95a12b3ed363653cb980588e2a9188cb8: equal nonzero-value multisets give
equivalent fibers and a permutation of supports. This proof idea is credited;
no colleague proof text or replacement partition definition is copied.
The original checkout remains unchanged, and redistribution licensing is not
assumed resolved. Prefer Mathlib equivalents when available.

The hard basis obligation is the finite symmetric coefficient expansion by
partition shape, then stable-range injectivity and a coordinate inverse. All
claims remain pending until local kernel proofs, statement review and full
integration checks pass.

## Implemented declarations

`SymmetricFunctions.exponentParts` is exactly the multiset of values on the
exponent support. Its sum, positivity, cardinal, multiset-multiplicity and
embedding formulas are proved. `MvPolynomial.coeff_msymm` is the stated
indicator formula; `isHomogeneous_msymm`, `killCompl_msymm`, and
`msymm_eq_zero_of_card_lt` prove homogeneity, deletion compatibility, and the
insufficient-alphabet case. `SymmetricFunction.zeroLast_eq_killCompl` identifies
the project's zero-last transition with Mathlib deletion, and `zeroLast_msymm`
proves the family compatibility.

The orbit module exports `exists_perm_of_exponentParts_eq`,
`exists_mapDomain_eq_of_exponentParts_eq`, `coeff_eq_of_exponentParts_eq`,
`Partition.exists_exponentParts`, `Partition.parts_card_le`,
`Partition.representative` and its shape/size laws, and
`MvPolynomial.eq_sum_msymm_of_representatives`. Representatives use Mathlib's
multiset occurrence type, retaining repeated occurrences, then an embedding
into a finite alphabet. The finite expansion works with ANY representatives.

`SymmetricFunction.monomialFamily` is the uniformly bounded compatible family
of Mathlib msymm; `mPart` is its inverse image under stableEquiv. The public
formulas are `rho_mPart`, `coeff_rho_mPart`, `isHomogeneous_mPart`, `mPart_zero`,
and `rho_mPart_eq_zero_of_card_lt`.

`monomialCoordinates` extracts coefficients in Fin d at fixed representatives;
`monomialSynthesis` forms the sum of scalar multiples of mPart.
`monomialSynthesis_coordinates` and `monomialCoordinates_synthesis` prove both
inverse laws. `monomialCoordinateEquiv`, `mBasis`, `mBasis_apply`, and
`mBasis_repr` package the homogeneous partition basis. `mBasis_repr_eq_coeff`
identifies coordinates at ANY exponent of the required shape in ANY finite
alphabet, without demanding N>=d. `mBasisAll`, `mBasisAll_apply`, and
`mBasisAll_repr` give the full basis through the existing homogeneous direct sum.

## Separate statement review

The implementing worker ran `scripts/ReviewMonomial.lean` and reviewed the
printed definitions and elaborated types independently of the proof scripts.
The stable lift is explicitly of the finite Mathlib orbit sum, not a renamed
elementary basis. Its coefficients use nonzero exponent VALUES, whereas the
elementary-basis partition adapter uses multiplicities at generator INDICES;
these two roles remain distinct. Equal parts give coefficient one, with no
factorial multiplier. Homogeneity is total alphabet degree d, transferred to
weighted symmetric-function degree. The finite formula includes every N and a.
The zero criterion uses the number of parts, not their sum. The basis and both
coordinate inverse laws assume only CommRing R, including zero and torsion
rings. Generic finite formulas even require only CommSemiring R. The arbitrary
representative coefficient formula explicitly proves independence of the
chosen representative. No statement or acceptance criterion was weakened.

## Validation and completion

- `python3 scripts/check_project.py`: exit 0, all 70 accepted modules built,
  root coverage passed, all 1,232 declarations passed the transitive axiom audit,
  notation and lambda simp regression scripts passed.
- `lake env lean scripts/ReviewMonomial.lean`: exit 0. Main coefficients,
  stable realization, homogeneous/full bases, and coordinate theorems depend
  only on propext, Classical.choice and Quot.sound.
- `lake env lean scripts/DeclarationIndex.lean`: exit 0; 929 noninternal
  accepted declarations indexed. MCP basis/example diagnostics were clean.
- `git diff --check`: passed. Examples cover the empty partition and alphabet,
  repeated partition (2,2) in two variables, vanishing in one variable,
  coefficient one in ZMod 2, and basis construction over both ZMod 2 and PUnit.
- A direct `decide` on the repeated exponent support did not reduce through
  classical support equality; the final example proves support by finite cases
  and simplifies explicitly. No native computation was used.
- No dependency updates, colleague proof text copied, or original-checkout edits.

Checked SHA-256: Finite/Monomial
`95c40b326ca791e7c07141c74119d17958f4ad8f92acd211c2e74406ce4ec9a1`;
Partition/Orbits `9d31d7785c09be56883d9af760544adb998b502bf28903749bd47113efcad439`;
Basis/Monomial `a1906a80f89955193605421b54bf4e1dd072d319479799339dceb304bee36e3d`.
All MONOMIAL criteria pass. RATIONAL is next. Completion/Schur/series extensions
remain outside the current goal and are not reported complete.
