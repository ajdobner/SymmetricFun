# Native foundation and extension API

This integration merges Alex Dobner’s main at `5b32dda` into the completed
extension work at `0bd3a94`. It preserves the upstream source tree verbatim and
adopts its Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 environment.
The previous environment was Lean 4.34.1 / Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.

## Design decisions

| Area | Decision and reason |
| --- | --- |
| Native carrier | Keep `MvPowerSeries.symmetricFunctionSubalgebra σ R`, including general alphabets and the CommSemiring foundation. It gives concrete coefficients and matches the original plan. |
| Grading | Keep upstream’s internal `symmetricFunctionGrading`; prove it matches weighted degree in the polynomial interface. No degree convention changes. |
| Polynomial interface | Retain `SymmetricFunction R` for the existing downstream theorem graph. Connect it through upstream’s proved fundamental theorem for arbitrary infinite σ and CommRing R, rather than replacing Alex’s implementation or silently rewriting existing contracts. |
| Permutations | Keep explicit renaming and upstream’s locally enabled actions; add no global action instances. |
| Partitions | Reuse `Nat.Partition` and upstream dominance. The old extension name `Partition.Dominates` becomes an abbreviation, with the same prefix-sum meaning. |
| Source layout | Preserve `SymmetricFun` and its native facade. Keep the large extension tree separate for review; both are default targets and fully audited. |
| Coverage | Permit transitive facade imports, matching upstream’s small umbrella file. Every accepted file must still be reachable and is explicitly built. Negative tests cover missing upstream imports and upstream proof holes. |
| Obsolete drafts | Accept all upstream removals of `SymmetricPoly`, fusion, and total-algebra drafts. |

## Public correspondence

Import `SymmetricFunctions.Compatibility.Upstream` for the bridge, or
`SymmetricFunctions` for the full extension library.

- `SymmetricFunction.upstreamEquiv σ R` identifies the polynomial interface with
  the native algebra for every infinite alphabet over a commutative ring.
- `upstreamEquiv_e` and `coe_upstreamEquiv_e` identify elementary generators,
  including the degree-zero convention.
- `upstreamEquiv_mem_grading_iff` and `upstreamEquiv_homogeneousComponent`
  identify the homogeneous pieces and their projections.
- `coe_upstreamEquiv` identifies the natural-alphabet map with `toSeries`.
- `upstreamEquiv_h` and `coe_upstreamEquiv_mPart` identify the existing complete
  and monomial functions on ℕ with upstream’s coefficientwise definitions.
- `boundedSymmetricSubalgebra_eq_upstream` proves equality of the two bounded
  subalgebras of the same actual series ring.

The existing extension declarations remain on their original type. Use the
algebra equivalence and its inverse to cross this boundary. This PR does not
claim that every extension is already re-exposed natively for arbitrary σ, nor
install competing global lambda or Hopf instances on the native subtype.
A systematic native API migration can therefore be reviewed separately without
changing the underlying mathematics or discarding closed proofs.

## Review and validation

See `handoffs/UPSTREAM-INTEGRATION.md` for the exact checks and source state.
The root proof audit covers all three libraries, including upstream declarations
that the bridge does not use. The historical task handoffs retain the environment
and source hashes at which those milestones were originally checked.
