# Initial core release integration and audit

- Task: RELEASE; owner: Codex (single worker); status: done.
- Prerequisites: HBASIS 3dae479, HOPF 00cc4cf, LFREE a71e8ee,
  STABLE e257846, BASE 9a38147. Other core tasks are also complete.
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- Scope: root import, consolidated Examples, local declaration index and this
  audit; supporting Transport and Examples/Torsion for a concrete torsion test.
- Reuse: pinned Mathlib's `TrivSqZeroExt`, `ZMod`, polynomial induction,
  ring morphisms, integer modules, and power-series units, together with the
  accepted polynomial lambda operations. No new colleague source was copied;
  upstream provenance remains in the existing source headers and reuse audit.

## Acceptance contract and review plan

Build every accepted module and affected examples; verify root import coverage.
Review the exact bounded stable equivalence, standard Hopf formulas, and
free special lambda-ring equivalence with all coefficient/target quantifiers.
Audit all accepted declarations transitively, allowing only standard Lean
foundations and no holes, custom axioms, or native_decide.

Consolidate examples for degree zero, empty alphabets, h_2, p_2, Delta(e_2),
S(e_2), and lambda_n(e_1)=e_n. Publish a local declaration index. Optional
research tasks remain planned and are not initial-core-release gaps.

## Concrete torsion-target validation, reviewed before implementation

Use Mathlib's trivial square-zero extension D = Z plus ZMod 2, with epsilon
=(0,1), so epsilon is nonzero, 2*epsilon=0, epsilon^2=0. Define total exterior
powers of (a,b) as (1+t)^a*(1+(0,b)t), an actual unit series with integer a.
The square-zero relation makes the second factor additive in b. Prove that
evaluating the already-special integer one-variable polynomial ring at epsilon
preserves all operations and is surjective. Descend the pre-lambda and special
laws along that map using fully proved transport lemmas. Only then instantiate
the free evaluator at epsilon and check its elementary images and nonzero
order-two value. This does not assume a finite ring has a special structure:
D has characteristic zero and a nonzero additive torsion ideal.

## Exported interface and integration

`LambdaRing/Transport.lean` exports `PreLambdaRing.ofSurjective` and
`SpecialLambdaRing.ofSurjective`. Both require an actual surjective ring map
and a proof that every exterior-power operation is preserved. They prove the
target laws by lifting its elements; they add no assumptions to the library.

`SymmetricFunction.Examples.Torsion` exports `Target`, `epsilon`,
`targetTotal`, `targetOperation`, `projection`, `projection_surjective`,
`projection_totalUnit`, `projection_operation`, and `projectionLambdaHom`.
The target has actual `PreLambdaRing` and `SpecialLambdaRing` instances.
`epsilon_ne_zero`, `epsilon_sq`, and `two_smul_epsilon` prove its nonzero
square-zero order-two element. `evaluation` is the universal lambda morphism;
`evaluation_e_one` and `evaluation_e_two` give epsilon and zero respectively.
The canonical right-integer scalar action and centrality instances needed by
Mathlib's square-zero extension are constructed from the usual integer action.

`SymmetricFunctions/Examples.lean` consolidates all requested conventions with
`SymmetricFunction` locally irreducible. The examples cover degree zero, the
empty alphabet, h_2, p_2, the middle term in Delta(e_2), S(e_2), every
lambda_n(e_1), universal elementary evaluation, and a nonzero value killed by 2.

`docs/DECLARATIONS.md` is the curated entry-point guide. The generated
`docs/declarations.tsv` lists 800 noninternal accepted declarations by module,
name, and kind; it excludes private/internal names and anonymous examples.
The full transitive audit covers these as well: 1,039 declarations in total.
`scripts/DeclarationIndex.lean` regenerates the deterministic index.
`scripts/ReviewRelease.lean` reproduces the principal elaborated-type review,
instance checks, and representative axiom reports.

## Separate final mathematical statement review

Reviewer: Codex, single worker, in a pass over elaborated declarations and
referenced definitions separate from the proof scripts. This is a local
statement review, not a claim of external or second-person review.

- `SymmetricFunction R` is still polynomial-backed with positive elementary
  indices. Public e/h indices include zero. Grading assigns weight n to e_n;
  ordinary degree in the elementary generators has not replaced that weight.
  Partition bases use Mathlib `Nat.Partition`, not the inherited replacement.
- `stableEquiv R` assumes only `CommRing R`. Its target consists exactly of
  compatible symmetric polynomials under zero-last-variable maps and the
  uniform quantifier `exists d, forall N, totalDegree(f N) <= d`. The bound
  is a proposition, not extra data. `stableEquiv_symm_eq_lift` uses any N>=d,
  including the zero-degree and empty-alphabet cases. It asserts nothing
  about the unrestricted inverse limit or completed symmetric series.
- The actual `HopfAlgebra R (SymmetricFunction R)` instance synthesizes for
  arbitrary `CommRing R`. All tensor products in its structure are over R.
  Delta(e_n) and Delta(h_n) sum over i+j=n, the counit is 1 at index zero
  and 0 at positive indices, and S(e_n)=(-1)^n h_n. Positive power sums
  are primitive without division by their index. The total tensor grading
  counts both factor degrees, and degree zero is linearly equivalent to R.
  Coefficient naturality and integral base change retain their full scope.
- `PreLambdaRing` specifies exterior powers, with lambda_0(a)=1 and
  lambda_1(a)=a. `SpecialLambdaRing` is a property of these operations using
  the independently constructed integral P/Q polynomials, including the
  explicit unit law and every zero-index product/iteration case. The signed
  polynomial operations and the stable source special instance are proved.
- `lambdaHomEquiv A` assumes exactly `CommRing A`, `PreLambdaRing A`, and
  `SpecialLambdaRing A`. It has no Nontrivial, IsDomain, CharZero, Algebra Q,
  or torsion-free assumption. Its forward map evaluates at e_1; its inverse
  is built for every a:A and sends each e_n to lambda_n(a).
  `lambdaEvaluation_preserves` covers every source element and operation
  index; `lambdaEval_natural` covers arbitrary preserving target morphisms.
  This is freeness on one generator. The target is never rationalized.
- The concrete torsion target has its special laws descended from the
  already-proved polynomial instance along a proved preserving surjection.
  Its nonzero element killed by 2 is verified in the actual ring. No finite
  ring or desired preserving morphism is postulated to make the example work.

The review found no contract weakening, circular premise, or additional
mathematical assumption. No downstream contract revision was needed.

## Validation and completion

Exact source state checked: the RELEASE completion commit containing this
handoff. All implementation files were final before the full checker; only
documentation and task-status updates followed it.

- `python3 scripts/check_project.py`: exit 0; all 55 accepted modules built
  cleanly (2,100 build jobs including dependencies), root import coverage
  checked, and all 1,039 accepted declarations transitively axiom-audited.
  The allowed foundations are only propext, Classical.choice, and Quot.sound.
  The lexical check also rejects proof holes, custom proof axioms,
  native_decide, and inherited-draft imports in the accepted library.
- `python3 scripts/test_check_project.py`: exit 0; all five tests passed.
- `lake env lean scripts/ReviewRelease.lean`: exit 0. Hopf and actual torsion
  special instances synthesize. Direct axiom reports for stableEquiv,
  comultiplication_e, lambdaHomEquiv, projectionLambdaHom, and
  evaluation_e_two use only the three allowed Lean foundations.
- `lake env lean scripts/DeclarationIndex.lean`: exit 0; 800 declarations
  indexed. The index is local; no external publication occurred.
- Lean MCP diagnostics for Transport, Examples/Torsion, and Examples:
  empty, with complete elaboration and no failed dependencies.
- Final `python3 scripts/check_project.py --static-only` and
  `git diff --check`: exit 0. All task prerequisites are complete.
- Pinned dependencies are unchanged. The original colleague checkouts were
  not edited. The inherited `SymmetricPoly` drafts remain outside acceptance.

All RELEASE acceptance criteria pass, and the initial core goal is complete.
There are no unresolved core proof goals. PLETH and MONOMIAL are the next
ready research extensions; RATIONAL, SERIES, SCHUR, and COMPLETION retain
their prerequisites. BLUEPRINT and PLATFORM remain optional. None was
implemented or represented as complete during this core run.

## Recovery and useful implementation notes

Resume from the completion commit on `codex/symmetric-functions-foundation`.
The working tree is intended to be clean at that checkpoint. No continuation
is needed for the core release; a separately authorized extension should
begin by selecting its registry entry and writing its contract/handoff.

For the torsion example, using the square-zero extension avoids assuming that
an arbitrary finite ring admits special exterior powers. The signed series
projection follows from polynomial additive induction and the fact that
epsilon^k is 1, epsilon, or zero. Broad simplification of the chosen ZMod
representative can obscure its natural cast; the explicit `ZMod.cast_eq_val`
step in the surjectivity proof resolves it. Review/index scripts must run
after rebuilding the root so that new declarations are visible.
