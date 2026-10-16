# Degree completion, Omega, and valid evaluation

- Parent task COMPLETION; owner Codex (single worker); status done.
- SERIES complete at 2fa2390; COMP-ALG complete in the following checkpoint. Pins unchanged.
- Subtasks COMP-ALG, COMP-SERIES, COMP-OMEGA, COMP-HOPF, COMP-SUBST preserve
  every original parent acceptance criterion; see docs/tasks.json.

## Reviewed mathematical contract before implementation

The completed type is the product `∀ n : ℕ, homogeneousSubmodule R n` over
arbitrary CommRing R. Its multiplication has degree-n component
`∑ (i,j) in antidiagonal n, F_i * G_j`, with membership proved by weighted
homogeneity. Zero-degree scalars provide the R-algebra structure. Bounded
functions embed by their homogeneous components, injectively. Truncation is
the finite sum of components through a specified degree, and multiplication
agrees below that degree. The completion is algebra-equivalent to permutation-
invariant MvPowerSeries ℕ R, with no uniform bound imposed.

`completeSeries` has component h_n. Scoped Ω denotes this completed element;
ω continues to denote the bounded elementary-complete involution. The signed
series with component (-1)^n e_n is a two-sided inverse, by the existing finite
convolution identities. The completed tensor target must count both factor
degrees, allow infinite total-degree support, and use finite antidiagonal
convolution. Extend the actual Hopf coproduct and prove Ω group-like there;
no ordinary algebraic tensor-product codomain assertion is allowed.

Completed evaluation requires a proved coefficient-finiteness or filtration
hypothesis. Mathlib HasSubst includes both constant-term and family-finiteness
conditions, and its underlying dummy function outside these conditions must
never be exposed as a valid evaluation. Bounded agreement and useful Ω examples
are required. Merely inverting every 1-t^k does not establish convergence of Ω.
No unrestricted infinite plethysm is part of this contract. No rationality is
needed for the general completion or Hopf results.

Detailed interfaces and statement reviews were recorded in each subtask handoff
before long proof searches, followed by validation. All subtask criteria and
integrated examples now pass, as recorded below. SCHUR remains outside this run.

## Completed implementation and final mathematical review

The five subtasks preserve all original parent acceptance criteria and the
additional user contracts. Their checkpoint history is:

- SERIES: 2fa2390, uniform bounded symmetric-series equivalence.
- COMP-ALG: c077926, weighted product algebra, bounded embedding and truncations.
- COMP-SERIES: b90e0a5, algebra equivalence with all symmetric multivariate series.
- COMP-OMEGA: 9d5214d, completed complete/elementary series, inverses and notation.
- COMP-HOPF: 36f3f9f, completed total tensor, bounded compatibility and group-like Ω.
- COMP-SUBST: the final checkpoint containing this handoff, certified evaluations
  and their finiteness, filtration and bounded-agreement proofs.

A final separate pass using scripts/ReviewCompletion.lean read the definitions and
elaborated mathematical statements without relying on compilation as evidence of
their intended meaning. It checked:

| Contract | Implemented evidence and mathematical interpretation |
| --- | --- |
| Uniform, proof-irrelevant bounded realization | HasBoundedTotalDegree is ∃D before all exponent vectors; boundedSeriesEquiv is an R-algebra equivalence. Bound and symmetry are propositions in a subtype. Actual exponent-orbit coefficients and e/h/m finite formulas are preserved. |
| Product of weighted homogeneous components | DegreeCompletion is GradedCompletion of the original homogeneousSubmodule. Component multiplication is the finite antidiagonal sum. e_n has degree n, not one. |
| Algebra, embedding and truncation | completionEmbedding is an algebra map with a separate injectivity proof. Inclusive truncation through D preserves components below D, kills higher ones, and commutes with products after truncating the output. |
| Identification with all symmetric series | completionSeriesEquiv is onto permutation-invariant MvPowerSeries ℕ R with no uniform bound. Its inverse reconstructs each bounded homogeneous layer. Finite restrictions land in formal series, not necessarily polynomials; there is no inverse-limit-of-finite-polynomial-rings identification. |
| Ω and generating identities | completeSeries has component h_n; signedElementarySeries has (-1)^n e_n. Both product orders equal one. The other elementary/signed-complete identity is also proved. Ω is opt-in notation on the completed type, distinct from ω. |
| Completed coproduct | CompletedTensor is the product of the original total tensorDegree pieces. completedCoproduct preserves components and commutes with the bounded coproduct via tensorCompletionMap. Ω is group-like in this target, not in an asserted ordinary algebraic tensor of completions. |
| Valid completed substitutions | completedSubstitution requires HasSubst; its coefficient formula has a finite-support proof. Finite positive alphabets and infinite locally finite positive alphabets are certified. Truncation formulas prove the filtration argument. All agree with bounded evaluation. |
| Examples and limits | First Ω components, inverse signs, empty/finite alphabets, degree-two coproduct, torsion/zero rings, one-letter geometric inversion and increasing powers are checked. Positive degree alone for an infinite repeated alphabet is disproved. No unrestricted infinite plethysm, nor Omega evaluation from denominator units alone, is exposed. |

Every general SERIES/COMPLETION result retains arbitrary CommRing R. No rational
assumptions were introduced here. The foundational polynomial-backed type, pinned
dependencies, original theorem contracts, and reference checkouts are preserved.
No colleague proof text was copied; reuse attribution is in REUSE_AUDIT and SERIES.

## Final validation and source state

- `python3 scripts/check_project.py`: exit 0; 89 accepted modules built, including
  all modules outside facade import paths, and all 1,652 declarations checked for
  transitive axioms. Only propext, Classical.choice and Quot.sound occur.
- `python3 scripts/test_check_project.py`: exit 0; five tests passed.
- `lake env lean scripts/ReviewCompletion.lean`: exit 0; reviewed all parent
  contract statements and principal transitive dependencies separately.
- The five subtask review scripts and SERIES review passed at their checkpoints.
- Lean MCP diagnostics for final substitution code: clean; notation displayed-goal
  and scope tests pass through the integration checker.
- `lake env lean scripts/DeclarationIndex.lean`: 1,233 indexed public/noninternal
  declarations. `git diff --check`: clean. Final registry static check passes.

Exact implementation source hashes (SHA-256) are below, complementing the subtask
handoffs. The final checkpoint containing this handoff is the checked source state.
- `SymmetricFunctions/Realization/SeriesBasic.lean`: `a717de2fe0a4e79fa79aa914b4d22a56626ba786db27ff99d1b58f2986f91904`
- `SymmetricFunctions/Realization/PowerSeries.lean`: `344d33170ee537f2cc74ac22b5094d32b897149cf73a9e16622cd37593c1da04`
- `SymmetricFunctions/Completion/Graded.lean`: `ee228c2a27f2e62e77e51155f2820178cabb034d949147c91e495f053fe8aa97`
- `SymmetricFunctions/Completion/Basic.lean`: `c3442e96c0f23def1c15455b0729a9f6319f0a972f089d7cdbfb78df4e954c78`
- `SymmetricFunctions/Completion/Realization.lean`: `c14da4b001036f839ab48bcb9845b1223bc7fccd651428c8ef2e723cd8434548`
- `SymmetricFunctions/Completion/Omega.lean`: `5cd42a9903059513cb538b47b23a24378cfe4746396c5958a0b56f4c41f634ea`
- `SymmetricFunctions/Completion/Single.lean`: `656c5c9e6177b2f00c99a123398981cc879685b29ebfbc0b74edb46c997dbc3b`
- `SymmetricFunctions/Completion/Hopf.lean`: `f1abb0366800663fce25a4a995d92e7edc7c59f39933ecc53ac0fd3b9fd5bef0`
- `SymmetricFunctions/Completion/Substitution.lean`: `e096601985757e264185ef03ac3f378b1462e17af4094cb7fdff610fad43981f`
- `SymmetricFunctions/Completion.lean`: `fe6eac708e072def6e549de1a8e709a2d226c076b2c9f3c4069900d359092110`
- `SymmetricFunctions/Notation.lean`: `fa1df9e51f443363f3b95cfe1d3f0bb2faf0098d40dbc58c7991b7be67abd6a4`

## Remaining scope and next action

No SERIES or COMPLETION acceptance obligations remain. SCHUR is ready by its
prerequisites and intentionally unclaimed; begin its exact registry contract and
statement review in a subsequent run. BLUEPRINT and PLATFORM remain optional,
with external uploads/publication unauthorized. Additional completed lambda/Hopf
structures or more general convergence theorems are not asserted by this API.
The overall symmetric-functions project is not complete.
