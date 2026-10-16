# Jacobi–Trudi determinants

Task SCHUR-JT; owner Codex (single worker). Implementation begins after SCHUR-PART
validation. Dependencies SCHUR-PART, HBASIS, SPEC; coefficient rings arbitrary.

## Declarations and mathematical review before proof search

- `completeInt (k : ℤ) : SymmetricFunction R` is h_(k.toNat) if 0≤k, zero otherwise.
  In particular completeInt 0=1, completeInt (-1)=0; negative indices are NOT h_0.
- `jacobiTrudiMatrix (ξ : Nat.Partition d) (L : ℕ) : Matrix (Fin L) (Fin L) (SymmetricFunction R)`
  has entry `completeInt ((Partition.rowLength ξ i : ℤ) - (i : ℤ) + (j : ℤ))`.
- `schur ξ` is the determinant at L=Partition.length ξ. It is an actual determinant,
  not a relabeling of another basis or a rational definition.
- `det_jacobiTrudiMatrix ξ hL` identifies the determinant for every L≥length ξ
  with schur ξ. The proof appends a row (0,…,0,1), using zero padding.
- `isHomogeneous_schur ξ : IsHomogeneous (schur ξ) d`: each nonzero permutation
  term has degree sum_i (ξ_(σ i)-σ i+i)=d. A term with any negative index is zero.
  The total is symmetric-function weight, not elementary polynomial degree.
- `map_schur φ ξ` for all coefficient homomorphisms R→+*S.
- `rho_schur N ξ`: the finite image is the same determinant of the integer extension
  of Mathlib hsymm. This is an algebraic finite specialization, not a tableau claim.
- Empty determinant=1; one row schur(indiscrete n)=h n; one column
  schur((indiscrete n).conjugate)=e n by the integral h/e recurrence.

All definitions permit the zero ring and rings with torsion. Sufficient padding
includes the actual length and the empty partition at padding zero. There is no
restriction on the finite alphabet size in rho_schur.

## Reuse search and intended proofs

Pinned Matrix determinant expansion, RingHom/AlgHom.map_det, det_succ_row,
Fin.succAbove_last, and det_fin_zero/one/two. Existing map_h, rho_h, h/e convolution,
and the public weighted homogeneous submodules. Search results found no pinned
Schur/Jacobi–Trudi implementation. No colleague code copied.

### Matrix helper review before the one-column proof

`SymmetricFunctions.upperToeplitz N F` will send a formal PowerSeries A to the
N×N upper triangular matrix with (i,j) entry coeff_(j-i)(F) if i≤j, zero otherwise.
This is a ring homomorphism: multiplication uses the finite bijection
k ↦ (k-i,j-k) from i≤k≤j to the antidiagonal of j-i. The conditional prevents
truncated subtraction from introducing entries below the diagonal. Its determinant
is coeff_0(F)^N. A finite matrix identity is sufficient; no series evaluation or
analytic convergence is involved. Apply it to H(u)E(-u)=1, then the classical
adjugate minor formula gives the one-column determinant. This remains integral
and permits the zero ring. Ownership extends to Schur/Toeplitz.lean and
Schur/Column.lean; these are helpers within SCHUR-JT, not new assumptions.

## Accepted results and separate statement review

Every declaration proposed above is now proved, including the column formula
`schur_indiscrete_conjugate`. The helper `upperToeplitz_complete` connects guarded
natural coefficient differences with the public integer convention. ReviewSchur
prints the actual definitions and contracts: negatives are zero; all matrix
subtractions occur after integer casts; padding has the exact lower bound;
homogeneity uses the existing weighted submodule; map/rho statements retain
arbitrary rings and all finite alphabet sizes. The column proof cancels a unit
sign, not a nonzero scalar, and therefore works in torsion and zero rings.
No tableau interpretation or general conjugation theorem is claimed here.

## Validation and exact checked state

Base 5a9ca9d plus this checkpoint; SHA256:
- Schur/JacobiTrudi.lean: 8f98372a0f71e2dac8c1b2a17347058de800c8fb5c526db1044ba74950c74933
- Schur/Toeplitz.lean: 215831792c03fad57ba2e296169f6813d289cffa405d9ef1108ee3ee3f0c1d92
- Schur/Column.lean: da78b5f3dbdc620b35a7be225630237d792e80c71c843baf048ddc94488450b0
- Examples/JacobiTrudi.lean: a6c7e336087f9520ff0090f8b3a948a845120c27736d2b3396afb3f2ab6c30b7

`python3 scripts/check_project.py`: exit 0, 95 accepted modules, all 1,751
declarations pass the transitive axiom audit; notation and lambda checks pass.
`python3 scripts/test_check_project.py`: exit 0, five tests.
`lake env lean scripts/ReviewSchur.lean`: exit 0; definitions and types reviewed
separately, representative axioms only propext/Classical.choice/Quot.sound.
Lean MCP Column diagnostics: success with no errors or warnings.
Examples cover negative/zero integer indices, empty padded determinants,
(2,1), padding to seven rows, ZMod 6, the zero ring, columns, and vanishing of a
column under an insufficient finite alphabet.

No SCHUR-JT obligations remain. Next SCHUR-BASIS is an integral transition proof;
it must not replace the determinant by an unrelated chosen basis.
