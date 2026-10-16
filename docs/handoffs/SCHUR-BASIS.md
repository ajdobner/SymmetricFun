# Integral Schur bases

- Task SCHUR-BASIS; owner Codex (single worker); status in_progress.
- Prerequisites SCHUR-JT (b67fc85), HBASIS, MONOMIAL complete.
- Assigned Schur/Triangular.lean, Basis/Schur.lean; pins unchanged.

## Proposed declarations and statement review before proof search

`Partition.squareWeight ξ := (ξ.parts.map (fun n => n^2)).sum` is an ordering
statistic, NOT symmetric-function degree. Degree is still the partition size.
`jacobiTrudiIndex ξ σ i : ℤ := rowLength ξ (σ i) - (σ i : ℤ) + (i : ℤ)`.
For every nonidentity permutation, the sum of squares of these integer indices
is strictly greater than squareWeight ξ. No nonnegativity is needed for this
inequality. When all indices are nonnegative they define a partition of d via
Nat.Partition.ofSums; the corresponding determinant term is its actual hPart.
Negative indices give a zero term by the already proved completeInt API.

Define `schurCompleteTransition R d μ ξ` as the hBasis-coordinate at μ of
`⟨schur ξ, isHomogeneous_schur ξ⟩`. Prove diagonal entries 1, and entries 0
when μ≠ξ and squareWeight μ≤squareWeight ξ. Thus every diagonal block for the
square-weight statistic is an identity matrix; strict off-diagonal terms move
in one direction. Prove the finite transition determinant is 1 integrally.

`schurBasis R d : Module.Basis (Nat.Partition d) R (homogeneousSubmodule R d)`
has value schur ξ, with only `[CommRing R]`. `schurBasisAll R` is the direct-sum
basis indexed by `Σ d, Nat.Partition d`, also with the actual determinant values.
Provide the coordinate expansion and uniqueness through these bases. Include
torsion and zero-ring examples. No rational scalar extension or relabeling of
an existing basis is used to define Schur functions.

## Proof search and intended integral argument

Pinned Mathlib has the weak rearrangement inequality
`Antivary.sum_mul_le_sum_comp_perm_mul`. Writing a_i=ξ_(σ i)-σ i+i gives
sum a_i² = sum ξ_i² + sum(i-σ i)²
             + 2*(sum ξ_(σ i)*i - sum ξ_i*i).
The last term is nonnegative by decreasing rows, and the sum of squares is
strictly positive for a nonidentity permutation. This proves the exact
triangular direction, including repeated rows. Zero entries are then removed
by the existing Nat.Partition.ofSums constructor, not a new partition type.
Use Mathlib matrix determinant/basis equivalence over a commutative ring and
the established graded direct sum to construct the actual Schur bases.

This is a reviewed proposed strategy, not yet an accepted result. The main
remaining obligation is connecting determinant terms to hBasis coordinates.

## Accepted implementation and separate mathematical review

All proposed basis contracts are proved. `schurCompleteTransition_eq_delta_of_le`
states the exact triangular direction, with identity blocks for equal square
statistics. `det_schurCompleteTransition` proves determinant one using those
blocks. `schurBasis` applies Mathlib's integral unit-determinant basis criterion
to the actual determinant vectors. `schurBasisAll` uses the existing weighted
direct sum; no rational argument or coefficient localization occurs.
`sum_schurBasis_repr`, `sum_schurBasisAll_repr`, and `ext_schur_coefficients`
provide expansions and uniqueness. `schurBasisAll_repr` identifies each degree's
coordinates with the existing homogeneous decomposition.

The separate ReviewSchur output confirms all ring assumptions are just CommRing,
that basis values are the previously defined determinants, and that squareWeight
is only a triangular-order statistic. Same-statistic distinct partitions have
zero transition entries, so the statistic need not be injective. The strict
integer sum-of-squares argument covers repeated rows; negative determinant
indices are discarded only after proving their factors zero. Degree zero and
empty matrices are included. No orthogonality, tableau formula, or positivity
is claimed by this checkpoint.

## Validation and exact source state

Base b67fc85 plus this checkpoint. SHA256:
- Schur/Triangular.lean: f2cff4cc26b3bec62e45a7ea4e92b3836945f49cbc491d2503f7d66c6109eec2
- Basis/Schur.lean: a392ac788a5659c85e5f97e08c5b19a6ad37af051532f1be1e56ad3efb4060cb
- Examples/SchurBasis.lean: 9569c2c63d80aff2e8b2a9c71486761023afc7d399d3cdb7ee7507b82dd9d5c2

`python3 scripts/check_project.py`: exit 0, 98 accepted modules and 1,810
transitively audited declarations; notation and lambda regressions pass.
`python3 scripts/test_check_project.py`: exit 0, five guard tests.
`lake env lean scripts/ReviewSchur.lean`: exit 0; mathematical statements reviewed
separately, with only approved standard axioms for both bases.
Examples instantiate the homogeneous basis over ZMod 6 and PUnit, compute the
empty full-basis vector and repeated-row (2,2) determinant, and distinguish
squareWeight 8 from symmetric-function degree 4.

No SCHUR-BASIS obligations remain. Next SCHUR-DUAL; Hall, skewing, and Cauchy are
still open. `squareWeight` is not a replacement for the grading or a positivity
result.
