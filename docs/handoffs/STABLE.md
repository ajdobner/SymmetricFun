# Bounded stable symmetric polynomial realization

- Task: STABLE; owner: Codex (single worker); status: done.
- Prerequisite: FINITE ac261f7.
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- Scope: SymmetricFunctions/Stable.lean, root/docs.
- Sources: accepted finite stable range and Mathlib subalgebra/Pi algebra API.
  No colleague code copied.

## Mathematical contract and proposed interface

For every CommRing R, define a subalgebra of the product over N of the symmetric
N-variable polynomial algebras. Membership means BOTH
`∀ N, transition N (f (N+1)) = f N` AND
`∃ d : ℕ, ∀ N, (f N).val.totalDegree ≤ d`.
The degree bound is existential propositional data, not a chosen bound stored in
the mathematical object. Addition uses a maximum bound; multiplication uses a sum.
Construct `stableEquiv R : SymmetricFunction R ≃ₐ[R] BoundedStable R` with
`stableEquiv R f N = rho R N f`. Prove its inverse can be computed by
`liftSymmetric R N (family N)` for every uniform bound d and every N≥d. Deduce
independence from both the chosen bound and stable alphabet.

## Pre-proof statement review

This is the uniformly bounded compatible subalgebra, not the unrestricted inverse
limit and not completed symmetric series. There is one d for all alphabet sizes,
with no chosen bound in the subtype. All maps fix R and preserve multiplication.
The inverse equality must hold for every permissible bound/alphabet, including
zero, and the resulting family must agree in small as well as stable alphabets.
No Nontrivial R, characteristic, flatness or torsion restrictions are permitted.

## Strategy

Compatibility transports equality downward between alphabet sizes. Lift a
family at a stable size and use the bounded equality test to compare lifts.
Use a common larger alphabet to establish all component equations. Package the
bijective specialization algebra map. Final review and validation passed.

## Exported declarations and separate statement review

Exports in `SymmetricFunction`: `Compatible`, `UniformlyBounded`,
`boundedStableSubalgebra`, `BoundedStable`, `mem_boundedStableSubalgebra`,
`Compatible.eq_of_le`, `compatible_rho`, `uniformlyBounded_rho`, `stableMap`,
`stableMap_apply`, `stableMap_injective`, `rho_liftSymmetric_of_le`,
`liftSymmetric_eq_of_le`, `rho_liftSymmetric_of_bound`, `stableMap_surjective`,
`stableEquiv`, `stableEquiv_apply`, `stableEquiv_symm_eq_lift`,
`liftSymmetric_independent`, and `rho_stableEquiv_symm`.

The implementing worker separately reviewed the elaborated main types, the
membership predicate and subalgebra fields. BoundedStable is explicitly a Type
abbreviation for the subalgebra's carrier subtype, so all algebraic structures
are inherited. Its sole data is the family; compatibility and the existential
uniform bound are proofs. The order of the quantifiers is ∃d,∀N, not ∀N,∃d.
The forward equivalence has the exact specialization at every N. Its inverse
formula works for every bound d and every N≥d, and liftSymmetric_independent
compares two possibly different bounds and stable alphabets. Component recovery
includes every smaller alphabet and N=0. All results retain arbitrary CommRing R;
no characteristic, nontriviality or torsion assumptions were introduced.
No mathematical contract changes were required.

## Validation and completion

- Lean MCP final diagnostics: clean, no errors or warnings.
- `lake env lean .scratch/StableReview.lean`: exit 0; types separately reviewed;
  ring and algebra instances also synthesized for PUnit coefficients.
- `python3 scripts/check_project.py`: exit 0; all 16 accepted modules built cleanly,
  all 398 accepted declarations passed the transitive axiom audit.
- `git diff --check`: passed; root includes Stable.
- Examples cover e 0 and inverse/forward recovery in the empty alphabet,
  with the public type locally irreducible.

All STABLE acceptance criteria passed. The bounded stable realization is now
proved. It is not the unrestricted inverse limit or a degree completion.
NEWTON is selected next; LPOLY is also ready. Hopf and special lambda structures,
the free special lambda-ring theorem, and RELEASE remain open.

Checked Stable.lean SHA-256:
`6392e00d6d26a53402a4efa20e4a2556569707f345b1e7fff572716a4bb6ac9c`.
