# Certified completed evaluations

- Task COMP-SUBST; owner Codex (single worker); status done.
- Prerequisites COMP-SERIES b90e0a5, COMP-OMEGA 9d5214d, RATIONAL done.
- Scope Completion/Substitution.lean, examples and notation documentation; pins unchanged.

## Precise proposed declarations and statement review

For a : Nat -> MvPowerSeries τ R with a proved Mathlib HasSubst a,
`completedSubstitution a ha : DegreeCompletion R ->ₐ[R] MvPowerSeries τ R`
is substAlgHom ha composed with completionToSeries. Expose the actual finite
support and finsum formula for every output coefficient. A sufficient certificate
is zero constant term for every a_i and finiteness of {i | coeff d a_i ≠ 0}
for every d; for finitely many source letters the second condition is automatic.
Neither positivity alone for an infinite alphabet nor arbitrary unit denominators
are sufficient. All maps require certificates before evaluating anything.

For a : Fin N -> MvPowerSeries τ R with zero constant terms,
`completedFiniteEval a h0` first restricts to Fin N and then substitutes. Prove
agreement with MvPolynomial.aeval a (rho R N f) on embedded bounded f, and with
the public SF.eval whose elementary images are those finite elementary polynomials.
For the infinite certified map, also prove bounded evaluation from its specified
elementary images. These are coefficient-linear R-algebra maps; they do not claim
to give an unrestricted lambda-compatible plethysm on completions.

For zero constant terms, prove truncation through D of the output depends only
on input components through D. Use the pinned truncTotal_subst theorem's actual
hypotheses (and finite target alphabet where Mathlib requires it). This is the
filtration argument that makes coefficient finiteness transparent. Identity-letter
substitution, empty alphabet, Omega inverse preservation, and positive-degree
examples will exercise the API. A one-letter Omega evaluation should give the
geometric inverse of 1-a, with constantCoeff a=0 proved or assumed explicitly.

Review: the source has no degree bound; operations are never exported through bare
MvPowerSeries.subst without a certificate. General results have CommRing R only;
there is no rationality or torsion-freeness assumption. Formal scaling, virtual
negation and coefficient conventions remain as documented. Invertibility of all
1-t^k from RATIONAL does not itself justify applying these maps to Omega.

## Reuse search

Pinned MvPowerSeries.Substitution provides HasSubst (nilpotent constants and
coefficientwise finite families), hasSubst_of_constantCoeff_zero for finite source,
substAlgHom, substAlgHom_coe, coeff_subst_finite, coeff_subst, subst_self, and
truncTotal_subst_eq_truncTotal_subst_sum. Use these proved APIs with all hypotheses.

## Exported declarations and separate statement review

`hasSubst_of_positive_locallyFinite`, `hasSubst_positivePowers`,
`completedSubstitution`, `completedSubstitution_coefficient_finite`,
`coeff_completedSubstitution`, `completedSubstitution_embedding`,
`completedFiniteEval`, `completedFiniteEval_embedding`,
`completedFiniteEval_embedding_eq_eval`, `truncTotal_completedSubstitution`,
`truncTotal_completedFiniteEval`, `finite_signedElementarySeries_truncate`,
`completedFiniteEval_signedElementary_one`, `completedFiniteEval_complete_one_mul`.
Identity-letter and inverse-preservation lemmas are also public. The implementation
bridges ending in _apply are explicit rewrites, not default simp rules; the public
identity-letter, bounded-input and one-letter rules therefore retain useful forms.

ReviewCompletedSubstitution inspected definitions and elaborated types separately
from the proofs. The generic map requires the actual Mathlib HasSubst certificate,
including both nilpotent constants and coefficientwise finiteness. The strict
positive version proves zero constants imply nilpotence. For finite alphabets
Mathlib proves the family condition from finiteness of Fin N. For increasing
powers X^(n+1), nonzero coefficient d forces n+1=d.degree, bounding the relevant
indices. No rational, domain or nontriviality condition is imposed on evaluations.
The negative example uses integers to exhibit an actual forbidden infinite family.

The coefficient finsum is accompanied by its finite-support proof. The filtered
truncation theorems assume zero constants and Finite τ, the latter only for the
polynomial-valued truncation codomain; the evaluation maps allow arbitrary τ.
Bounded agreement is proved both via the public elementary evaluator and concretely
by finite polynomial aeval. The one-letter Omega identity proves inversion of
1-a under zero constant coefficient, not merely from denominator invertibility.

## Validation and exact checked state

- `python3 scripts/check_project.py`: exit 0; final source builds 89 accepted
  modules cleanly, all 1,652 declarations pass transitive axiom checks, and notation
  and lambda simplification regressions pass. Only ordinary Lean foundations.
- `python3 scripts/test_check_project.py`: exit 0; all five tests passed.
- `lake env lean scripts/ReviewCompletedSubstitution.lean`: exit 0; separate
  interface and transitive-axiom review.
- `lake env lean scripts/ReviewCompletion.lean`: exit 0; parent contract review.
- Lean MCP diagnostics for Completion/Substitution: clean; goal inspection confirms
  the identical-infinite-letter rejection reduces to finiteness of Nat being false.
- `lake env lean scripts/DeclarationIndex.lean`: 1,233 indexed declarations.
- Examples check identity letters, bounded evaluation, finite-degree dependence,
  Omega's geometric inverse for X and X² over ZMod 2, the genuinely infinite
  increasing-power alphabet, and rejection of infinitely repeated X over integers.
- `git diff --check`: clean. Dependency pins unchanged; no reference repositories
  modified and no external uploads or publication performed.

No COMP-SUBST obligations remain. The Completion.lean facade imports the completed
coproduct and certified substitution APIs. Parent acceptance is recorded in
COMPLETION.md; SCHUR and optional external work are left for subsequent runs.

Checked source hashes (SHA-256):
- `SymmetricFunctions/Completion/Substitution.lean`: `e096601985757e264185ef03ac3f378b1462e17af4094cb7fdff610fad43981f`
- `SymmetricFunctions/Examples/CompletedSubstitution.lean`: `04608a6a5d28b650515f2eef9cbca7bfabc490a6d15dc2b1f4c98ab3f73c1de8`
- `SymmetricFunctions/Completion.lean`: `fe6eac708e072def6e549de1a8e709a2d226c076b2c9f3c4069900d359092110`
