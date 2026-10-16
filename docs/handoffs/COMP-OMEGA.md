# Completed complete and elementary generating series

- Task COMP-OMEGA; owner Codex (single worker); status done.
- Prerequisites COMP-ALG c077926, COMP-SERIES b90e0a5, COMPLETE done; pins unchanged.
- Scope Completion/Omega.lean, optional Notation module, examples, documentation.

## Precise proposed declarations and statement review

`completeSeries : DegreeCompletion R` has component n equal to h_n, with its
membership certificate supplied by isHomogeneous_h. `elementarySeries` similarly
has e_n. `signedElementarySeries` and `signedCompleteSeries` have (-1)^n times
the respective homogeneous component. Prove both orders of E(-X)H(X)=1 and
E(X)H(-X)=1 using the existing finite degree convolutions, and package the complete
series as a unit with the explicit signed elementary inverse.

Scoped Ω denotes `completeSeries` with inferred coefficient ring. It has completed
type, never bounded type; ω remains the elementary-complete involution. The signed
elementary series is a degree sign operation; its use here must not suggest that
formal variable scaling and virtual alphabet negation have identical power sums.
Finite specialization is the already justified coefficient restriction map to
MvPowerSeries (Fin N) R. Prove its degree-n complete/elementary components are
finite h_n/e_n, and check first components and empty alphabets. All CommRing R.
General substitution and completed coproduct remain separate required subtasks.

## Reuse and proof strategy

Use component extensionality, finite antidiagonal multiplication, e_h_convolution,
h_e_convolution and their signed counterparts. Search finite hsymm/esymm coefficient
lemmas before adding any orbit formula. No infinite plethystic evaluator is assumed.

## Exported API and separate statement review

All four named series and their component lemmas are implemented. Both orders of
`signedElementarySeries_mul_completeSeries` and
`elementarySeries_mul_signedCompleteSeries` are proved. `completeSeriesUnit`
exposes the inverse without assuming a field. `homogeneousComponent_completedFiniteSpecialization`
commutes finite restriction with each component;
`homogeneousComponent_finite_completeSeries` and the elementary analogue identify
actual finite polynomials. `completedFiniteSpecialization_zero_completeSeries`
is the empty-alphabet identity.

A separate inspection with ReviewOmega checked completeSeries' completed carrier,
its h_n components, the signs and both multiplication orders. All general results
require only CommRing R. The notation scope imports without activation and keeps
Ω distinct from bounded ω. The finite map is restriction, already justified by
SERIES and COMP-SERIES; no unrestricted substitution is introduced. The examples
check degrees 0–3, degree-1 and degree-2 inverse signs, truncation through 2,
torsion and zero rings, finite h_2 and the empty alphabet.

## Validation

- `python3 scripts/check_project.py`: exit 0; 83 accepted modules built and
  transitive axioms of 1,588 declarations checked (ordinary foundations only).
- `python3 scripts/test_check_project.py`: exit 0; five tests passed.
- `lake env lean scripts/ReviewOmega.lean`: exit 0, definitions/types reviewed
  separately from proof compilation; unit and finite specialization axiom checks.
- Lean MCP diagnostics for Completion/Omega: clean.
- CheckNotation verifies displayed Omega goals, inference/precedence, scope
  isolation, and rejection of bounded Omega and bounded plethysm on Omega.
- `lake env lean scripts/DeclarationIndex.lean`: 1,182 indexed declarations.

No COMP-OMEGA gaps. COMP-HOPF and COMP-SUBST remain required for the parent.

Checked source hashes (SHA-256):
- `SymmetricFunctions/Completion/Omega.lean`: `5cd42a9903059513cb538b47b23a24378cfe4746396c5958a0b56f4c41f634ea`
- `SymmetricFunctions/Notation.lean`: `fa1df9e51f443363f3b95cfe1d3f0bb2faf0098d40dbc58c7991b7be67abd6a4`
- `SymmetricFunctions/Examples/Omega.lean`: `3d15f33d2d93b111e4855f092eb1c296771c4bee413a15f328f450b82e732a8d`
- `scripts/CheckNotation.lean`: `6537b3abf218559d42d3e65bff0e759d3bb686c20a2b8a33cbd35bd285092121`
