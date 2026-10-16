# Coproduct into the completed tensor target

- Task COMP-HOPF; owner Codex (single worker); status done.
- Prerequisites COMP-ALG c077926, COMP-OMEGA 9d5214d, HOPF complete; pins unchanged.
- Scope Completion/Single.lean and Completion/Hopf.lean, examples and review.

## Precise proposed declarations and statement review

`CompletedTensor R := GradedCompletion (tensorDegree R)` is the product of the
proved total-degree tensor submodules in SF R ⊗[R] SF R. Degree d counts i+j=d
in both tensor factors. Its multiplication uses the finite total-degree
antidiagonal. It is not the algebraic tensor product of two completions.

`completedCoproduct : DegreeCompletion R →ₐ[R] CompletedTensor R` extends the
existing coproduct componentwise using comultiplication_mem_tensorDegree.
`completedTensorLeft` and `completedTensorRight` similarly extend the ordinary
factor inclusions. Their product defines the completed external tensor F⊠G,
whose component n is ∑i+j=n F_i⊗G_j. Prove
`completedCoproduct completeSeries = completedTensorProduct completeSeries completeSeries`
by the existing coproduct formula for h_n.

Build `tensorCompletionMap : SF R ⊗[R] SF R →ₐ[R] CompletedTensor R`
by the tensor universal property from the bounded embeddings of the two factors.
Prove it agrees with single-degree inclusion on homogeneous tensor elements, then
prove the bounded coproduct square commutes on elementary generators. This checks
agreement with the actual existing coproduct rather than introducing an unrelated
map sharing only an informal formula. All results use CommRing R, including zero.

Review: the total tensor degree was proved before this task; no assumption of
coassociativity or tensor grading decomposition is added. No map is asserted to
land in an ordinary tensor product of completions. Generic single-degree elements
will be proved using the auxiliary PowerSeries realization and its monomials.

## Exported declarations and separate statement review

`CompletedTensor`, `CompletedTensor.component_mul`, `completedCoproduct`,
`component_completedCoproduct`, `completedTensorLeft`, `completedTensorRight`,
`completedTensorProduct`, `component_completedTensorProduct`,
`tensorCompletionMap`, `component_tensorCompletionMap_of_mem`,
`completedCoproduct_embedding`, `completedCoproduct_completeSeries`.
Single.lean supplies generic single-degree elements, their convolution and naturality.
The bounded tensor compatibility proof uses homogeneous pure tensors and span
induction, then checks the bounded algebra square on elementary generators.

A separate ReviewCompletedHopf pass inspected the target definition, both tensor
degrees, the component formulas and bounded agreement before considering the
proof bodies. The group-like identity is in the product of total tensor pieces.
It does not assert an ordinary tensor-product target for two completed series.
The original comultiplication algebra map appears explicitly on the bounded side.
All coefficient rings are arbitrary CommRing R. No new Hopf or grading instance
is postulated. `tensorCompletionMap` is named as a map; injectivity of this auxiliary
map is not asserted or needed for the parent acceptance criteria.

## Validation and exact checked state

- `python3 scripts/check_project.py`: exit 0; 86 accepted modules and transitive
  axiom audit of 1,625 declarations, only ordinary Lean foundations.
- `python3 scripts/test_check_project.py`: exit 0; five tests passed.
- `lake env lean scripts/ReviewCompletedHopf.lean`: exit 0; target, elaborated
  statements and principal transitive axioms inspected separately.
- Lean MCP diagnostics for Completion/Hopf: clean.
- `lake env lean scripts/DeclarationIndex.lean`: 1,209 indexed declarations.
- Examples compute Omega's degree-zero and degree-two coproduct, verify general
  bounded agreement, and place e_2 tensor e_3 in degree five, not degree two.

No COMP-HOPF gaps remain. COMP-SUBST is the last implementation subtask before
final parent acceptance review and integrated validation.

Checked source hashes (SHA-256):
- `SymmetricFunctions/Completion/Single.lean`: `656c5c9e6177b2f00c99a123398981cc879685b29ebfbc0b74edb46c997dbc3b`
- `SymmetricFunctions/Completion/Hopf.lean`: `f1abb0366800663fce25a4a995d92e7edc7c59f39933ecc53ac0fd3b9fd5bef0`
- `SymmetricFunctions/Examples/CompletedHopf.lean`: `ae050c1d0e197fa2a6669f71014933ca69ece5153989dfa6cb17b4cc39e0bc07`
