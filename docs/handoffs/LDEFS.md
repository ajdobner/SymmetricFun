# Exterior-power lambda-ring definitions

- Task: LDEFS; owner: Codex (single worker); status: done.
- Prerequisite: LPOLY f49cd2f.
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- Scope: LambdaRing/Defs.lean, LambdaRing/Hom.lean.
- Search: pinned Mathlib has no PreLambdaRing or SpecialLambdaRing declaration;
  reuse RingHom, FunLike/RingHomClass, finite antidiagonals, and the proved LPOLY.
  No colleague code is copied.

## Mathematical contract and proposed formal interface

`PreLambdaRing A` assumes only `[CommRing A]` and supplies operations
`LambdaRing.lambda : Nat -> A -> A` with lambda_0(a)=1, lambda_1(a)=a,
and lambda_n(a+b)=sum_(i+j=n) lambda_i(a)*lambda_j(b).
Derive lambda_n(0)=if n=0 then 1 else 0 from these axioms.

`SpecialLambdaRing A` is a proposition on an existing PreLambdaRing instance.
Its fields are the unit law lambda_n(1)=if n<=1 then 1 else 0; the product
law lambda_n(ab)=P_n evaluated at the positive lambda values of a and b,
in that order; and iteration lambda_n(lambda_m(a))=Q_(n,m) evaluated at the
positive lambda values of a. Every n,m ranges over all natural numbers.

`LambdaRingHom A B` extends a unital RingHom and preserves every lambda_n.
Provide FunLike and RingHomClass instances, extensionality, identity,
composition, forgetful evaluation, and identity/associativity laws. Morphisms
are defined already for pre-lambda rings and apply unchanged to special ones.

## Pre-proof statement review

The chosen convention is exterior powers, not symmetric powers: lambda_t(1)=1+t.
There is no torsion-free, Nontrivial, or characteristic restriction. The special
property does not posit a desired preserving morphism or free object. Its
product polynomial has two ordered positive-variable blocks; iteration has one.
At n=0 both identities reduce to 1=1. At m=0, iteration becomes the unit law
because Q_(n,0) is 1 for n<=1 and zero otherwise. Positive indices occur only
inside polynomial substitution; lambda_0 is explicitly 1. Separate operations
from specialness so LLINE does not claim LSPECIAL's obligations prematurely.

## Validation plan

Review elaborated class fields and morphism statements independently of proofs.
Check zero-input and zero/one-index formulas and a zero-ring example if useful.
Run Lean MCP diagnostics, the full project/axiom checker and checker tests;
update exports, status, and this handoff only after acceptance passes.

No implementation has yet been accepted at this initial handoff.

## Implemented interface and final review

Defs exports `PreLambdaRing`, `LambdaRing.lambda`, `lambda_zero`, `lambda_one`,
`lambda_add`, the derived `lambda_zero_input` and `lambda_neg_convolution`;
`SpecialLambdaRing` is a Prop-valued class on a pre-lambda instance and exports
`lambda_unit`, `lambda_mul`, and `lambda_iterate` through namespace LambdaRing.
Hom exports `LambdaRingHom` extending RingHom, FunLike and RingHomClass,
`map_lambda`, `ext`, `toRingHom_injective`, `id`, `comp`, their evaluation and
forgetful-map laws, and left/right identity and associativity.

Separate statement review by the same worker used fully elaborated signatures
in `.scratch/LDefsReview.lean`. The three PreLambdaRing axioms are exactly the
zero-index, one-index and addition laws. The special fields use the fixed
integral P_n and Q_(n,m) in the correct block order, quantify over every n,m,
and impose no torsion restriction. The special class adds no operations,
preventing competing operation instances. The morphism constructor requires
preservation for every n and every input; extensionality forgets only proof data.
Accepted examples check both nested zero-index conventions, including
lambda_2(lambda_0(a))=0. Zero-input follows by induction and additive cancellation,
not from an extra axiom or integer cancellation. This task constructs no
nontrivial special instance and makes no claim about LSPECIAL.

Validation of the exact source state in this completion commit:
- `python3 scripts/check_project.py`: exit 0; 40 accepted modules built and
  root-import checked; 791 declarations passed the transitive axiom audit.
- `python3 scripts/test_check_project.py`: exit 0, five tests passed.
- `lake build LambdaRing.Hom`: exit 0, both new modules clean.
- `lake env lean .scratch/LDefsReview.lean`: exit 0; reviewed signatures and
  direct axiom checks use only the standard allowed Lean foundations.
- Lean MCP diagnostics for Defs and Hom: empty.
- `git diff --check`: exit 0.

All LDEFS acceptance criteria pass. LLINE is ready. No dependency changes,
new proof axioms, or copied colleague code. Special polynomial identities for
negative coefficients and freeness for torsion targets remain later obligations.
