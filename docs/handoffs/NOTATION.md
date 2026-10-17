# Readability and notation

- Task: NOTATION; owner: Codex (single worker); status: done.
- Prerequisites: OMEGA ce87705, LFREE a71e8ee, NEWTON fde87d5; current
  accepted core checkpoint 09f6408.
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- Scope: Names, Notation, Examples/Notation, CheckNotation, conventions guide,
  registry/root/index; a separately recorded minimal PLETH substep.
- Reference inspected read-only: `/home/ghseeli/flagged-llt-polynomials/Flagged
  plethysm and LLTs.tex`, symmetric-functions and plethystic-evaluation sections
  (lines 590–805), especially labels e:Omega, ss:plethysm, ss:coefficients.
  No source or proof is copied from the paper or colleague checkout.

## Mathematical contract, before implementation

Use ordinary scoped notation activated by `open scoped SymmetricFunctionNotation`:
`Λ[R]` denotes the existing polynomial-backed bounded symmetric-function type;
`ω f` denotes its elementary-complete involution; `λ[n] a` denotes the existing
exterior-power operation on any PreLambdaRing; `f⟦g⟧` denotes integral plethysm
for f,g in SymmetricFunction Z. No new coefficient or target instance is inferred
from CommRing alone. Lambda indices remain natural, including zero.

Add descriptive, definitionally equal aliases for elementary, complete, powerSum,
and elementaryCompleteInvolution. Retain the established e/h/p/omega declarations
and their lemmas unchanged. Do not broadly rename standard mathematical names.

Integral plethysm is exactly `lambdaEval g f`. Before syntax tests, prove
`plethysm (e 1) g = g`, `plethysm f (e 1) = f`, and
`plethysm (plethysm f g) k = plethysm f (plethysm g k)` by the existing
universal evaluator, without any new mathematical premise. Document that the
rest of PLETH (Adams formulas and tensor lambda compatibility) is unfinished.

Uppercase Omega is reserved for the degree-completed sum of h_n. Neither the
bounded ring nor the auxiliary one-variable generating series is that completed
type. No Omega declaration/notation or infinite evaluation is introduced.

## Pre-proof statement review and reuse search

The implementing worker read the paper's definitions separately from the planned
proofs. The paper's rational coefficient-linear power-sum evaluation fixes outer
coefficients; parameters occurring inside the alphabet undergo power substitution.
Virtual negation gives p_k[-X]=-p_k[X]; scaling indeterminate letters gives
p_k[tX]=t^k p_k[X], whose later t=-1 specialization differs in even degrees.
Integral lambda evaluation does not supply arbitrary coefficient-linear evaluation.
Disjoint alphabets are separately symmetric, represented through tensor products.

Lean MCP local search found no plethysm declaration and confirmed lambdaEval_natural,
lambdaEval_self, and omega_involutive. Pinned Mathlib scoped notation patterns were
inspected; its unrelated scopes already use omega and double brackets, so all new
syntax must require an explicit project scope. Plain declarations remain available.

## Validation plan

Compile exact declarations before longer proofs. Check parsing by definitional
equalities, nested expressions by associativity, scope isolation and displayed
goals by regression examples. Check actual proof goals through Lean MCP. Run the
full project checker, regenerate the declaration index, and record the separate
final statement review and exact checked commit. No claims of completion yet.

## Final interface and independent statement review

The pre-proof plan above is complete. `Names.lean` exports the four descriptive
aliases with the same instances and indices as their existing declarations.
`Notation.lean` uses four ordinary scoped notation declarations; there is no
custom parser/elaborator or alphabet-expression language. The new integral
plethysm definition and eight API theorems are recorded in PLETH's handoff.

The implementing worker separately inspected the elaborated types with
`pp.notation false` in `.scratch/NotationReview.lean`, including the complete
definition of plethysm. Both operands are SymmetricFunction Int and the result
is lambdaEval of the inner argument applied to the outer argument. The
associativity statement has the intended orientation; lambda preservation
is in the outer argument. No additivity in the inner argument, rational
coefficient generalization, or completed substitution is asserted.

The aliases preserve CommSemiring for elementary and CommRing for complete,
powerSum, and the involution. PowerSum remains positive-indexed. Exterior
notation has precisely CommRing and PreLambdaRing assumptions; specialness
is required only by the existing theorems that use it. The test also exercises
the actual torsion target from RELEASE. Existing names and instances are
unchanged. Uppercase Omega has no definition or notation.

The guide's general power-sum convention formulas explain the paper's
mathematics; they are explicitly distinguished from the currently proved
degree-two examples and the remaining PLETH/RATIONAL obligations. The paper
source SHA-256 is
`024860e828b16348b453ee28dd1d8bc249ffb1c3c78fd09d34a7e4f41456f727`.

## Validation and completion

Exact checked source state: the completion commit containing this handoff.

- `lake build SymmetricFunctions.Plethysm.Integral SymmetricFunctions.Names
  SymmetricFunctions.Notation`: exit 0 before dependent notation examples.
- `python3 scripts/check_project.py`: exit 0, 59 accepted modules, all 1,067
  declarations audited transitively; only the allowed standard Lean foundations.
  The full checker now also runs `scripts/CheckNotation.lean`.
- `python3 scripts/test_check_project.py`: exit 0, five tests passed.
- `lake env lean scripts/CheckNotation.lean`: exit 0. Exact displayed-goal
  assertions pass for Lambda, omega, lambda, and nested plethysm. Expected
  failures verify import/section scope isolation, absence of uppercase Omega,
  rejection of rational-coefficient plethysm, and no fabricated lambda instance
  on an arbitrary coefficient ring. These command tests are outside the accepted
  import graph; all accepted proof declarations remain hole-free.
- `lake env lean .scratch/NotationReview.lean`: exit 0; separate full-type and
  direct axiom checks of plethysm associativity and exterior-power preservation.
- Lean MCP diagnostics for Examples/Notation: empty. MCP goal inspection in
  CheckNotation confirms the exact symbolic goals asserted by the display tests.
- `lake env lean scripts/DeclarationIndex.lean`: exit 0; 818 noninternal
  declarations indexed. The guide links these to the underlying descriptive API.
- `git diff --check` and the final static registry/root check: exit 0.
  Dependencies and original checkouts remain unchanged.

All NOTATION criteria pass. Full PLETH is still in progress, with Adams and
tensor lambda/Hopf compatibility explicitly unproved. RATIONAL and COMPLETION
remain planned; this readability request does not complete those milestones.

## Useful failed approach

Writing omega as application notation (`omega` followed by a term) parsed
correctly but its generated unexpander did not match the inserted algebra-
equivalence coercion: goals printed `omega (omega f)`. Notation for the
equivalence constant itself fixes the display without a custom delaborator.
The guarded goal regression prevents reintroducing that readability failure.
