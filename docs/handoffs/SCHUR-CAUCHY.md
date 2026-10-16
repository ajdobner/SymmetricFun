# The completed Schur Cauchy kernel

Owner Codex (single worker); proposed next task, after CAUCHY-FINITE validation.
Prerequisites HALL-SCHUR and SCHUR-SKEW complete; pins unchanged. Own Cauchy.lean,
Hall.lean and Examples/Cauchy.lean (registry to be updated upon claiming).

## Precise declarations and pre-proof review

`cauchySchurComponent R d := Σ_{λ : Nat.Partition d} schur λ ⊗ schur λ`.
Prove equality with the already constructed `cauchyCompleteMonomialComponent R d`.
Use the actual Hall form's two proved normalizations, not a new definition of
Schur functions or pairing. Tensor Schur coordinates give an explicit faithful
pairing test; this does not identify an infinite direct sum with its full dual.

`cauchyKernel R : CompletedTensor R` has component n equal to the complete/monomial
component n/2 if n%2=0 and zero otherwise. Prove its even component equals both
partition sums, its odd component is zero, and finite specialization equals
`finiteCauchyProduct (Fin M) (Fin N) R`. All R assumptions are CommRing, including
zero and torsion rings. The tensor completion is total degree; this is not an
ordinary algebraic tensor product of completions. The kernel is conventionally
Ω[XY], while the established completed coproduct of Ω concerns X+Y. No new
notation will imply an unconstructed unrestricted completed plethysm map.

Examples will check the zeroth, first, and second total components, the equal
Schur/h/m expansions, finite specialization, and torsion/zero-ring conventions.
Previously accepted examples already cover negative determinant indices, padding,
(2,1), conjugation, Hall duality and skew shapes. No tableau formula, positivity,
LR rule, or flagged/LLT statement is claimed. Parent SCHUR is complete only after
this final subtask's full integration, independent statement review, and axiom audit.
