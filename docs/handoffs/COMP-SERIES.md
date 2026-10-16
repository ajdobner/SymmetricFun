# Completion as symmetric multivariate series

- Task COMP-SERIES; owner Codex (single worker); status done.
- Prerequisites SERIES 2fa2390 and COMP-ALG c077926 complete; pins unchanged.
- Scope Completion/Realization.lean and examples/review documentation.

## Precise proposed declarations and statement review

`completionToSeries R : DegreeCompletion R →ₐ[R] MvPowerSeries ℕ R` has
coefficient at a equal to `coeff a (toSeries R (component R F a.degree))`.
It is symmetric, and its degree-n homogeneous series is exactly the image of
F_n. Prove multiplicativity using inclusive finite truncations: the coefficient
at a of a product sees only exponents b,c with b+c=a, hence degrees at most
a.degree. The finite bounded product identity therefore suffices, without
assuming any infinite summation theorem.

`completionSeriesEquiv R : DegreeCompletion R ≃ₐ[R] SymmetricSeries R`
is surjective because each homogeneous layer of a symmetric series is symmetric
and has the single uniform degree bound n. SERIES reconstructs that bounded
layer, and its homogeneous membership follows from the proved commutation of
homogeneous projections. Prove embedding agreement, component projection and
finite restriction compatibility. All hypotheses are CommRing R, including zero.

Review before proof search: total exponent degree matches weighted SF degree by
SERIES, and the infinite family has no uniform bound. The target is invariant
MvPowerSeries ℕ R; finite restrictions are power series, not necessarily finite
polynomials. This is not the unrestricted inverse limit of finite symmetric
polynomial rings. No infinite sum of bounded functions is claimed to be bounded.

## Reuse/search

Existing coeff_toSeries, toSeries_homogeneousComponent, boundedSeriesEquiv,
DegreeCompletion.homogeneousComponent_truncate and truncate_mul are central.
Pinned MvPowerSeries.Order supplies coeff_homogeneousComponent,
isHomogeneous_homogeneousComponent and coefficient vanishing. Multiplication
uses MvPowerSeries.coeff_mul and the finite exponent antidiagonal.

## Exported declarations and separate review

`completionToSeries`, `coeff_completionToSeries`, `completionToSeries_component`,
`completionToSeries_injective`, `completionSeriesEquiv`,
`completionToSeries_embedding`, `completedFiniteSpecialization`,
`completedFiniteSpecialization_embedding`, `coeff_completedFiniteSpecialization`.
The reusable reverse homogeneity criterion is `isHomogeneous_of_toSeries`.

The separate review script inspected the carrier, assembly function and all major
elaborated types. Surjectivity reconstructs actual bounded homogeneous layers,
not a chosen subset of symmetric series; there is no global bound on the product.
The algebra equivalence has only CommRing R, allowing torsion and the zero ring.
Its finite restriction target is MvPowerSeries (Fin N) R and bounded compatibility
holds at every N, with no stable-range restriction. Homogeneous components use
the same total exponent degree and original weighted SF grading. No assertion
about the unrestricted inverse limit of polynomial rings is made.

## Validation and exact state

- `python3 scripts/check_project.py`: exit 0; 81 accepted modules, transitive
  axiom audit of 1,560 declarations; only ordinary Lean foundations.
- `python3 scripts/test_check_project.py`: exit 0; all five tests passed.
- `lake env lean scripts/ReviewCompletionSeries.lean`: exit 0; reviewed statements
  independently of their proof bodies, and inspected principal axiom closures.
- Lean MCP diagnostics for Completion/Realization: clean.
- `lake env lean scripts/DeclarationIndex.lean`: refreshed accepted index.
- Examples exercise torsion and zero rings, homogeneous projection and finite
  specialization of arbitrary bounded inputs.

Use explicit component bridge lemmas rather than unfolding the polynomial-backed
SF type inside completed expressions. Bare definitional equality under toSeries
caused invalid projection or excessive reduction; the public lemmas avoid this.

No COMP-SERIES gaps remain. Next: COMP-OMEGA; then completed tensor and substitutions.

Checked source hashes (SHA-256):
- `SymmetricFunctions/Completion/Realization.lean`: `c14da4b001036f839ab48bcb9845b1223bc7fccd651428c8ef2e723cd8434548`
- `SymmetricFunctions/Examples/Completion.lean`: `8be56f303775ea63ddd848d17a37985e7373a1ebc37f57e084c8d3a940aa28c4`
