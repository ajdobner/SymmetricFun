# Schur orthonormality for the classical Hall pairing

- Owner Codex (single worker); status done; base ba58820.
- Prerequisites HALL-CORE, SCHUR-BASIS, SCHUR-DUAL complete.
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 unchanged.
- Owned files Finite/Bialternant.lean, Schur/AlternantPairing.lean, Hall/Schur.lean,
  Examples/HallSchur.lean. No reference checkout changes or colleague code copying.

## Precise proposed declarations and pre-proof mathematical review

All coefficient rings are arbitrary CommRing R. For a finite alphabet Fin N,
`staircaseAlternant N` is the determinant with entry X_j^(N-1-i).
`partitionAlternant ξ N` is the determinant with entry
X_j^(rowLength ξ i + (N-1-i)); i,j : Fin N. Since i<N the staircase exponent
is nonnegative. These are actual finite polynomials, not a new Schur definition.

For N≥Partition.length ξ, `bialternant_schur` must prove
`alphabetSpecialization R (Fin N) (schur ξ) * staircaseAlternant N =
 partitionAlternant ξ N`.
This is a multiplication identity valid even with zero divisors. No division
by a Vandermonde or rational descent is proposed. The proof factors the
Jacobi–Trudi matrix using coefficients of the elementary generating polynomial
in all variables except one. Its product with the complete series is the
geometric series in that remaining variable. Negative complete indices remain
zero; all determinant subtractions are in integers.

`hall_schur_eq_alternating_coeff ξ hN f` must identify hall(schur ξ,f) with
the coefficient at rowLength ξ i + (N-1-i) of staircaseAlternant N times the
finite specialization of f. Its proof expands the actual determinant and
uses HALL-CORE finite coefficient extraction. Nonnegative exponent conditions
and zero contributions from negative determinant indices must be proved.

`coeff_partitionAlternant` at another decreasing shifted partition exponent
must give a Kronecker delta (sufficient common padding). Strictly decreasing
shifted rows ensure only the identity permutation can contribute when shapes
coincide; the empty alphabet/empty partition case must be included.

`hall_schur_schur (ξ μ : Σ d, Nat.Partition d)` must prove
`hall (schur ξ.2) (schur μ.2) = if ξ=μ then 1 else 0`.
Provide homogeneous and full Schur-coordinate extraction and degreewise
orthonormality consequences. This proves the second classical normalization
of the existing Hall form, not a redefinition of the form.

Statement review: sufficient padding is explicit; finite specialization and
coefficient operations are ordinary polynomial operations. The polynomial-backed
bounded source, integer determinant indices, weighted degrees and arbitrary-ring
contract are unchanged. No tableau generating formula or positivity is asserted.

## Reuse search / strategy

Pinned Mathlib has Matrix.vandermonde and its determinant, determinant expansion,
coefficient and finite-product series APIs, but no Schur bialternant or Cauchy
double-alternant theorem was found. Reuse these and the accepted integer JT API.
The main outstanding obligation is the integral bialternant factorization and
its alternating coefficient functional. No statements in this task are yet
reported proved; update exact exports and validation at the checkpoint.

## Completed interface and independent statement review

The exact source exports are printed by scripts/ReviewSchur.lean. The proposed
interfaces are implemented: complete_matrix_mul, bialternant_schur,
hall_completeInt_product, hall_schur_eq_alternating_coeff,
coeff_partitionAlternant, hall_schur_schur, hall_schur, hall_schur_right,
hall_schur_homogeneous and hallHomogeneous_schurBasis.

Separate review of printed definitions/types (Codex): alternant exponents are
nonnegative row-plus-staircase exponents; the subtraction in complete_matrix_mul
is in integers, and finiteCompleteInt still vanishes on negative indices.
Bialternant_schur requires sufficient rows and asserts multiplication only;
no domain, field, rationality, or nonzero Vandermonde assumption is hidden.
The alternating coefficient theorem permits any bounded second argument.
Both shapes have sufficient common padding in coeff_partitionAlternant; sigma
equality includes partition size. Empty determinants and alphabets are valid.
Hall_schur_schur refers to the existing h/m pairing and actual JT Schur function.
No tableau identification, positivity, or infinite-algebraic-dual claim occurs.

## Validation

All exit 0: python3 scripts/check_project.py (114 accepted modules, 2,021
transitive axiom audits with only propext/Classical.choice/Quot.sound; notation
and lambda regressions); python3 scripts/test_check_project.py (five guards);
lake env lean scripts/ReviewSchur.lean; git diff --check.
MCP diagnostics clean for Bialternant and AlternantPairing. Examples/HallSchur
compiles with (2,1) against itself and a distinct row, ZMod 6 coefficients,
PUnit, empty alphabet, extra padding, negative determinant indices, and full
Schur coefficient extraction. Logs /tmp/hall-schur-{check,review}.log.
lake env lean scripts/DeclarationIndex.lean passed: 1,453 noninternal declarations.
MCP Examples/HallSchur diagnostics are clean after shortening one statement. All HALL-SCHUR acceptance criteria pass.

Useful proof choices: omit-one-variable elementary polynomials have degree<N,
so complete-series convolution is finite at the required matrix size. Matrix
multiplication and the empty-shape determinant compute the staircase factor.
The coefficient theorem uses determinant transpose to align row-oriented JT
indices with the monomial exponents; impossible divisibility matches a negative
complete index. StrictAnti plus a matching permutation gives StrictMono of that
permutation, hence Mathlib StrictMono.eq_id. No Cauchy–Binet or tableau theorem
is assumed. Use simp, rather than rw, to change an iff inside an ite with its
dependent Decidable instance.

Exact checked Lean source SHA-256:
- `Finite/Bialternant.lean`: `972d79d8dcaf4db6f4b8432b2b7a1416f6e180b94917b789cd8ea5b5941578e2`
- `Schur/AlternantPairing.lean`: `8d9560728a4f49535ec64f3ea0c766c0ada2e06d2e6184feda36192b1fc24efa`
- `Hall/Schur.lean`: `1e3e302e30014d54da8ad9757a8c34e1939efedb7f05ed99f00cbd66d22369dc`
- `Examples/HallSchur.lean`: `83d13df1780644e45bf35edb4696c3e7dc4420d6b10a4e4d0ba93e943c17a5d0`
