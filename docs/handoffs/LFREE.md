# Freeness on one generator for arbitrary special lambda targets

- Task: LFREE; owner: Codex (single worker); status: done.
- Prerequisite: LSTABLE 3ae3ccb.
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- Scope: LambdaRing/Preservation.lean, SymmetricFunctions/Lambda/Universal.lean.
- Reuse: public SF evaluation/induction/extensionality, lambda_e_one,
  integral P/Q identities, RingHom/Subring, and formal-series coefficient API.

## Mathematical contract and proposed interface

For every CommRing A, PreLambdaRing A, SpecialLambdaRing A and a:A, construct
`lambdaEvaluation a : SymmetricFunction Z ->+* A` sending each positive e_i to
lambda_i(a). Prove preservation of every lambda_n on every source element,
then package `lambdaEval a : LambdaRingHom (SymmetricFunction Z) A`.
Prove its value on every natural elementary index and at e_1, uniqueness among
lambda-preserving ring maps with that e_1 value, and
`lambdaHomEquiv A : LambdaRingHom (SymmetricFunction Z) A ≃ A`.
Prove naturality under every preserving target morphism and both evaluation laws.

## Pre-proof statement review

A is an arbitrary commutative special lambda ring, including targets with
additive torsion. No Algebra Q A, CharZero, IsDomain, Nontrivial, torsion-free
assumption, or existence of the desired preserving morphism is allowed.
This is freeness on the distinguished element e_1, not unpointed initiality.
Public e_0=1 and lambda_0(a)=1 must agree, although internal generators remain
positive. Preservation is required on arbitrary polynomial expressions,
not only on elementary generators.

## Reviewed proof decomposition

Define `PreservesAt phi a` for a ring map between pre-lambda rings. Addition
preserves this property by the convolution law. Negation preserves it because
total exterior-power series of a and -a are mutual inverses; this proof uses
only unit cancellation and is valid with torsion. In special rings, 1 preserves
it by normalization and multiplication by the integral product identity.
These elements therefore form a Subring. The integral iteration identity
shows closure under all lambda_m as well.

Construct lambdaEvaluation by the public polynomial-backed universal ring map.
It preserves all operations at e_1 by lambda_n(e_1)=e_n and its defining
values. Closure under iteration then gives every e_i; the subring and public
SF induction theorem give preservation on all source elements and constants.
Any preserving morphism has e_i image lambda_i(image e_1), so public generator
extensionality proves uniqueness and the equivalence. Naturality follows from
that same extensionality. This proof never rationalizes the target.

## Validation plan

Review fully elaborated universal statements and all target instances separately
from proofs. Run actual lambdaHomEquiv evaluation/identity examples, all accepted
module builds and transitive axiom checks, and update this handoff/status before
committing. A concrete target with nonzero torsion requires a proved instance;
constructing such a RELEASE convention example will not be replaced by assuming
an arbitrary finite ring has a special lambda structure.

No LFREE implementation is accepted at this initial handoff.

## Implemented interface and proof coverage

Preservation exports `LambdaRing.PreservesAt`, `totalSeries`, its addition and
inverse identities, the series criterion for preservation, preservation at
zero/one, closure under addition/negation/multiplication, `preservingSubring`,
and closure under every lambda_m. The negation proof uses uniqueness of
mutual inverses in a commutative formal-series ring; no integer is cancelled.

Universal exports `lambdaEvaluation`, values at all e_n, preservation at e_1
and at every source element, `lambdaEval`, `lambdaEval_e`, `lambdaEval_e_one`,
`lambdaHom_e`, `lambdaHom_ext`, `lambdaEval_unique`, `lambdaHomEquiv`, its
forward/inverse evaluation laws, `lambdaEval_natural`, `lambdaHomEquiv_natural`,
and `lambdaEval_self`. The public SF induction API proves preservation on all
expressions without unfolding the foundational representation.

## Separate final mathematical statement review

Codex read the fully elaborated declarations in `.scratch/LFreeReview.lean`
independently of the proof scripts. The exact target arguments of lambdaHomEquiv
are A, CommRing A, PreLambdaRing A, and SpecialLambdaRing A. There is no
Nontrivial, IsDomain, CharZero, Algebra Q, or torsion-free instance. The inverse
is constructed from an arbitrary a:A; it does not assume a preserving morphism.
The preservation theorem quantifies over every source f and every natural
operation index through PreservesAt. Naturality quantifies over arbitrary
preserving morphisms between arbitrary special targets. The distinguished
source element is e_1, and every e_n, including n=0, has the stipulated image.
The rational auxiliary code imported for the generic integral-evaluation lemma
is not used to rationalize or restrict A. The actual proof uses integral
product/iteration identities, addition, and inverse cancellation.

## Validation and completion

Exact checked state: the completion commit containing this handoff.
- `python3 scripts/check_project.py`: exit 0; 52 accepted modules built,
  root coverage verified, 994 declarations passed the transitive axiom audit.
- `python3 scripts/test_check_project.py`: exit 0; five tests passed.
- `lake env lean .scratch/LFreeReview.lean`: exit 0; type review and direct
  axiom checks of preservation, the equivalence, and naturality use only
  propext, Classical.choice, Quot.sound.
- Lean MCP final Universal diagnostics: empty; Preservation compiled cleanly.
- `git diff --check`: exit 0. Pins and original checkouts unchanged.
- Examples check the identity evaluator and equivalence inverse law using
  the actual source special instance and arbitrary special targets.

All LFREE acceptance criteria pass. RELEASE is now ready and is the remaining
core task. A concrete nonzero torsion target example, if supplied at RELEASE,
will use a proved special instance rather than a hypothetical finite-ring one.
