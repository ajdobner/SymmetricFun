# Public lambda simplification repair

- Task LSIMP; owner Codex (single worker); status done.
- Starting checkpoint 949463c; prior core checkpoint 09f6408 independently
  audited by the user. Prerequisites LSTABLE/LLINE/LFREE are complete.
- Lean v4.34.1, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- Files: Defs, Polynomial/Operations, Lambda/Structure, CheckLambdaSimp and
  checker integration; registry, declaration guide/index, and this handoff.

## Contract and pre-proof review

Keep `LambdaRing.lambda n a` as the public simplification form. Remove `[simp]`
from the two identity bridges to implementation operations, retaining their
names, statements and `rfl` proofs for explicit rewriting. Do not add competing
reverse global bridges. Public zero, first-power, zero-input, unit, and e_1
identities should fire without exposing implementation definitions.

Proposed signed public lemma for every commutative pre-lambda ring, including
torsion targets: `lambda_two_neg (a : A) : lambda 2 (-a) = a^2 - lambda 2 a`.
This follows from the degree-two addition convolution, using only additive
cancellation, not division. Provide polynomial public reductions for a positive
coefficient-one monomial and a negative coefficient-one monomial using the
existing signed-series construction. Preserve all polynomial implementation
lemmas and the canonical stable symmetric-function structure.

The polynomial algebra equivalence is not a lambda equivalence: a formal
elementary generator is not being made a line element. The e_1 generator
identity must still return e_n for every n, not zero in higher degrees.

Search: Lean MCP confirms both bridge declarations and no existing
lambda_two_neg; existing polynomial negative-monomial formulas are reusable.
Pinned Mathlib supplies finite-antidiagonal sums and ordinary ring reasoning;
the project's lambda classes and identities supply the mathematical laws.

## Validation plan

Reproduce the root-import failure before the edit. Compile the changes and
affected modules. Add root-import regressions for all-natural generator
indices, zero, unit, degree-two signed inputs, and explicit bridge usability.
Keep a simp normal-form guard for arbitrary source expressions. Run full
project checks and axiom audit, review exact elaborated statements separately,
regenerate the index, mark done only after checks, and commit before PLETH.

## Completed interface and separate review

Both existing bridges retain their exact statements and proofs; only their simp
attributes change. Public operations are the normal form, with no reverse global
bridge. Added `LambdaRing.lambda_two_neg` for arbitrary commutative pre-lambda
rings, and Polynomial's `lambda_monomial_one`, `lambda_X`,
`lambda_monomial_neg_one`, `lambda_neg_monomial_one`. The last is the simp form:
polynomial simplification first turns monomial m (-1) into -monomial m 1.

Separate elaborated-type review in `.scratch/LSimpReview.lean` confirms that
lambda_two_neg has no specialness, nontriviality, characteristic, or torsion-free
assumption; polynomial formulas quantify over every variable type and all natural
indices. No source lambda instance or foundational representation was changed.
The regression explicitly proves that polynomialEquiv does NOT preserve the
second exterior power of e_1: its image is X_2, whereas the polynomial exterior
power of X_1 is zero. Thus the two structures cannot silently be identified.

## Validation and completion

Exact source state: the LSIMP completion commit containing this handoff.
- Before repair, `lake env lean .scratch/LambdaSimpRepro.lean` failed with the
  reported goal `lambdaOperation 2 (e 1) = e 2`.
- `python3 scripts/check_project.py`: exit 0; all 59 accepted modules built
  cleanly; 1,072 declarations transitively axiom-audited. Root import coverage,
  forbidden proof tokens, notation regressions, and new lambda regressions pass.
- `scripts/CheckLambdaSimp.lean` runs on the root import and checks all-index
  generators, nesting, zero/unit, degree-two virtual negatives, actual torsion
  inputs, polynomial line/signed formulas, exact public syntactic normal forms,
  the algebra-versus-lambda distinction, and continued explicit bridge access.
- `lake env lean .scratch/LSimpReview.lean`: exit 0; direct axiom dependencies
  of the new signed formulas are only propext, Classical.choice, Quot.sound.
- Lean MCP Operations diagnostics: empty. Five project-guard tests pass.
- Declaration index regenerated; `git diff --check` passes. Dependencies and
  original checkouts unchanged.

All LSIMP criteria pass. Continue immediately with PLETH, then MONOMIAL and
RATIONAL in the active goal. None of those extension tasks is marked complete.

Useful implementation detail: a simp lemma on monomial m (-1) alone misses its
target after simplification of the argument. The negative-of-positive-monomial
lemma supplies the actual normal form. Two deliberate no-op simp guards locally
disable only the unused-tactic linter, to assert that arbitrary public operations
are not rewritten into implementation functions.
