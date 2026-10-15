# Elementary-complete involution

- Task: OMEGA; owner: Codex (single worker); status: done.
- Prerequisite COMPLETE at d64df18.
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- Scope: SymmetricFunctions/Omega.lean and Grading/Evaluation.lean, root/docs.
- Reference: Mathlib weighted homogeneous induction and polynomial evaluation;
  no colleague proof copied.

## Mathematical contract and proposed interface

For every commutative ring R, define `omegaHom := eval (fun i : ℕ+ => h i)`.
Prove omegaHom(e n)=h n and omegaHom(h n)=e n, including n=0, and that its
square is the identity on all symmetric functions. Package
`omega : SymmetricFunction R ≃ₐ[R] SymmetricFunction R`.
For every degree d, prove `IsHomogeneous (omega f) d ↔ IsHomogeneous f d`
and preservation/reflection of membership in degreeLE R d. Provide the restricted
linear equivalence on homogeneous pieces for HBASIS.

Supporting lemma: weighted homogeneous polynomial evaluation preserves degree
when every substituted variable has precisely its assigned weight. Derive the
public homogeneous evaluation theorem for symmetric functions. This is useful
also for finite specializations and does not add an EBASIS prerequisite.

## Pre-proof statement review

The inverse is the same map, not an independent unproved generator assignment.
Use COMPLETE's dual recurrence to prove the h-images; generator extensionality
then covers all elements. Preserve weighted degree for each homogeneous element,
including zero and arbitrary rings with torsion. No field or Nontrivial hypotheses.
The filtration remains a submodule. No contract revision is needed.

## Strategy and validation

Strong induction on h recurrence; use e_succ_h and map_sum/map_smul.
Use Mathlib weighted homogeneous induction for the grading lemma, then transport
through polynomialEquiv at that boundary. Final review and validation passed.

## Exported declarations and statement-only review

`SymmetricFunctions.weightedHomogeneous_aeval` works for arbitrary additive
commutative weight monoids and commutative coefficient semirings. The target
substitution polynomials must have precisely the source-variable weights.
`SymmetricFunction.isHomogeneous_eval` transports this to the public type.

Other exports in `SymmetricFunction`: `omegaHom`, `omegaHom_e`, `omegaHom_h`,
`omegaHom_comp_self`, `omega`, `omega_apply`, `omega_e`, `omega_h`, `omega_symm`,
`omega_omega`, `omega_involutive`, `IsHomogeneous.omega`,
`isHomogeneous_omega_iff`, `omega_mem_degreeLE`, `omega_mem_degreeLE_iff`,
`omegaHomogeneous`, `omegaHomogeneous_apply`, and `omegaHomogeneous_symm`.

The implementing worker reviewed `#check @...` output separately from proofs.
All omega declarations have only CommRing R, no nontriviality or characteristic
assumptions. The homogeneous and filtration equivalences hold in every degree;
the restricted map is an actual R-linear equivalence. Its inverse is omega itself.
The proof that h maps back to e uses the already proved inverse recurrence,
not a freeness assumption on h. No contracts changed.

## Validation and completion

- Lean MCP final diagnostics: clean for both new modules.
- `lake env lean .scratch/OmegaReview.lean`: exit 0; elaborated types reviewed.
- `python3 scripts/check_project.py`: exit 0; all 12 accepted modules built cleanly,
  all 275 accepted declarations passed the transitive axiom audit.
- Examples check omega(e 2) = e 1 squared minus e 2 and filtration preservation;
  the public type is locally irreducible.
- `git diff --check`: passed; both modules included in root coverage.
- SHA-256 Omega.lean:
  `af4b7ef53ff6fdf0dc7c763db60906c8b8de57c38f48c94088ccad4eb913c3b2`.
- SHA-256 Grading/Evaluation.lean:
  `5265e94f2cead0c839fa835c9a945aeee869ae69a8e9625a358cb844281980d2`.

All OMEGA acceptance criteria passed. No remaining OMEGA obligations.
HBASIS is selected next. FINITE and NEWTON remain ready; RELEASE remains open.
