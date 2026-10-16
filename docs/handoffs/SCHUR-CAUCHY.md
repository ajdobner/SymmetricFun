# The completed Schur Cauchy kernel

Owner Codex (single worker); done, base 371f79c. CAUCHY-FINITE validated.
Prerequisites HALL-SCHUR and SCHUR-SKEW complete; pins unchanged. Own Cauchy.lean,
Hall.lean and Examples/Cauchy.lean (registry updated).

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

## Completed checkpoint and independent statement review (2026-10-16)

All proposed interfaces are proved. `tensorHall_schur` identifies bounded tensor
coordinates, and `tensorHall_schur_ext` proves faithfulness. The same actual
Hall form has both previously established normalizations; finite degreewise
reconstruction proves `cauchySchurComponent_eq_completeMonomial`.
`cauchyKernel` is a product of total-degree tensor pieces, with components zero
in odd degrees and the size-d partition sum in degree 2*d.
`completedTensorSpecialization_cauchyKernel` identifies this actual completed
element with the proved finite inverse product. Public low-component lemmas
normalize degrees 0, 1 and 2 to 1, 0 and e_1⊗e_1.

Separate review (Codex): inspected the printed definitions, implicit assumptions,
tensor target, degree arithmetic, coefficient maps and final theorem statements
before accepting the checkpoint. Every coefficient hypothesis is CommRing;
there is no rationality, domain, Nontrivial, or positivity condition. The finite
sums use Nat.Partition d and the already defined Jacobi–Trudi determinants.
The full tensor coordinate test is nondegeneracy, not an identification with
an infinite algebraic dual. Ω[XY] is explanatory terminology only; no unproved
completed plethysm map or new evaluation syntax is exposed. The actual public
finite specialization is an algebra map with the coefficientwise finiteness
argument proved in CAUCHY-FINITE. The completed coproduct Ω[X+Y] is distinct.

Validation, all exit 0: python3 scripts/check_project.py (129 accepted modules,
2,179 transitive declaration axiom audits; only propext/Classical.choice/Quot.sound;
root coverage, notation and lambda regressions pass); python3 scripts/test_check_project.py
(five guards); lake env lean scripts/ReviewSchur.lean (independent contract review);
lake env lean scripts/DeclarationIndex.lean (1,566 noninternal declarations).
MCP Cauchy and Examples/Cauchy diagnostics clean. git diff --check clean.
Examples check low components, the degree-four expansion over ZMod 6, a zero-ring
kernel using proved tensor faithfulness, finite specialization, and Ω[X+Y]'s
different degree-one component. Logs /tmp/schur-final-{check,review}.log.
Pins unchanged relative to audited 9f0eaee; reference checkouts unchanged.

Exact checked source SHA-256 (base 371f79c plus these files):
- `SymmetricFunctions/Cauchy.lean`: `80242406cb8a78b6371e05d7e173d685c183649289d3f42aecc634a59cae1216`
- `SymmetricFunctions/Hall.lean`: `3cd534b39ee58d672c35744b76914990dd432f156a676b91b0e6acb405044581`
- `SymmetricFunctions/Examples/Cauchy.lean`: `919fa7193c47db47cae04ca03d6f93bd332206b5a298fcc4370fedc4958453ee`

No SCHUR-CAUCHY obligations remain. SCHUR-TABLEAU and positivity remain later work.
