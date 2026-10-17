# Weighted grading and degree filtration

- Task: GRADE; owner: Codex (single worker); status: done.
- Prerequisite API: commit `c62ade0` (PART also available there).
- Pin: Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- Scope: `SymmetricFunctions/Grading.lean`, integration and this handoff.
- Sources: pinned Mathlib weighted homogeneous and direct-sum APIs. No colleague code port.

## Mathematical contract and formal interface

For every commutative coefficient semiring (and hence every commutative ring),
assign weight i to the positive generator i. Define `IsHomogeneous f d` through
`polynomialEquiv` and Mathlib's `IsWeightedHomogeneous`. Define
`homogeneousSubmodule R d` as the inverse image of the weighted homogeneous
submodule. Provide a `GradedAlgebra (homogeneousSubmodule R)` instance and
`decompose : SymmetricFunction R ≃ₐ[R] ⨁ d, homogeneousSubmodule R d`.
Provide linear projections `homogeneousComponent d`, their membership and
projection laws, and finite reconstruction.

Important statements (elaborated and reviewed):

```lean
isHomogeneous_e (n : ℕ) : IsHomogeneous (e (R := R) n) n
IsHomogeneous.mul (hf : IsHomogeneous f m) (hg : IsHomogeneous g n) :
  IsHomogeneous (f * g) (m + n)
degreeLE (R) (d : ℕ) : Submodule R (SymmetricFunction R) :=
  ⨆ k ≤ d, homogeneousSubmodule R k
degreeLE_mul (m n : ℕ) : degreeLE R m * degreeLE R n ≤ degreeLE R (m + n)
exists_mem_degreeLE (f : SymmetricFunction R) : ∃ d, f ∈ degreeLE R d
isHomogeneous_zero_iff (f : SymmetricFunction R) :
  IsHomogeneous f 0 ↔ ∃ r, f = algebraMap R (SymmetricFunction R) r
```

## Statement review before proof search

The implementing worker checked that weight is the positive index, not ordinary
polynomial degree. `degreeLE` is a finite supremum of submodules, representing
finite sums of pieces in degrees at most d; it is not asserted to be a
subalgebra. Homogeneous zero is allowed in every degree. Degree-zero pieces
are constants without assuming R is nontrivial. Finite reconstruction and
exhaustion express bounded-degree functions, not completed series. No contract
revision is needed.

## Proof strategy

Reuse weighted grading through the polynomial presentation, and Mathlib's
internal direct sum for reconstruction. Derive filtration multiplication using
suprema and homogeneous multiplication. Prove exhaustion by public generator
induction. Derive the degree-zero statement from the weighted zero projection.

## Final statement review

Separate statement-only review by the implementing worker used `#check @...` on
`decompose`, `isHomogeneous_e`, `degreeLE_mul`, `mem_degreeLE_iff`,
`isHomogeneous_zero_iff`, and `exists_mem_degreeLE`. All quantify over arbitrary
commutative semirings without `Nontrivial` assumptions. The filtration also has
the proved characterization `f ∈ degreeLE R d ↔ ∀ k, d < k →
homogeneousComponent k f = 0`. The direct sum enforces finite support; the
existential degree bound quantifies over each element rather than imposing a
single bound on the whole ring. No mathematical contract was revised.

## Exported declarations

Namespace `SymmetricFunction`: `IsHomogeneous`, `homogeneousSubmodule`,
`mem_homogeneousSubmodule`, the graded-algebra instance, `decompose`,
`homogeneousComponent`, `homogeneousComponent_eq_decompose`,
`polynomialEquiv_homogeneousComponent`, `homogeneousComponent_mem`,
`homogeneousComponent_of_mem`, `homogeneousComponent_of_mem_ne`,
`sum_homogeneousComponent`, `isHomogeneous_zero`, `isHomogeneous_one`,
`isHomogeneous_algebraMap`, `isHomogeneous_e`, `IsHomogeneous.add`,
`IsHomogeneous.smul`, `IsHomogeneous.mul`, `IsHomogeneous.pow`,
`isHomogeneous_zero_iff`, `degreeLE`, `homogeneous_le_degreeLE`, `degreeLE_mono`,
`degreeLE_zero`, `e_mem_degreeLE`, `algebraMap_mem_degreeLE`, `degreeLE_mul`,
`mul_mem_degreeLE`, `mem_degreeLE_iff`, and `exists_mem_degreeLE`.

The grading instance is transferred at the representation boundary: the comap
through `polynomialEquiv` is definitionally compatible with Mathlib's instance.
Other proofs use the named presentation/projection APIs; they do not unfold the
public type. The examples make the public type locally irreducible.

## Validation and completion

- `python3 scripts/check_project.py`: exit 0; all six accepted modules built
  without warnings; transitive axioms of 135 accepted declarations audited,
  allowing only `propext`, `Classical.choice`, and `Quot.sound`.
- Lean MCP searches, goals, and final diagnostics succeeded; no diagnostics remain.
- `lake env lean .scratch/GradeReview.lean`: exit 0; statement-only inspection.
- Examples cover a homogeneous expression of degree two, a mixed-degree
  expression bounded by three, and arbitrary elements over a subsingleton ring.
- Source SHA-256: `71c8a135eaf2e6255e3226f13680a472a006820b2bc488391e3a10d395ce466c`
  for `SymmetricFunctions/Grading.lean`, based on `c62ade0`.
- `git diff --check`: passed. Root imports include Grading.

All GRADE acceptance criteria passed. No remaining GRADE obligations. Continue
with EBASIS; BASE, SPEC, and COMPLETE are also ready. The overall RELEASE goal
remains active.
