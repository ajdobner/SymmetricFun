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
