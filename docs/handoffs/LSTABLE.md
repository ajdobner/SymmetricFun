# Stable integral special lambda operations

- Task: LSTABLE; owner: Codex (single worker); status: done.
- Prerequisites: LSPECIAL ad8d550; STABLE e257846.
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- Scope: SymmetricFunctions/Lambda/Structure.lean.
- Reuse: stableEquiv, finite rho/zeroLast, polynomial operation naturality and
  degree bounds, actual polynomial special lambda instance. No colleague code copied.

## Mathematical contract and proposed interface

For each n and bounded compatible symmetric integer-polynomial family f, define
`lambdaFamily n f` by applying the finite operation to every component. Symmetry
follows from permutation naturality, compatibility from zero-variable substitution,
and a uniform degree bound d becomes the uniform bound n*d. The bound remains
existential proof data, not a chosen bound stored in the object.

Define `lambdaOperation n f` on SymmetricFunction Z by stableEquiv inverse of
lambdaFamily n (stableEquiv f). Prove the exact finite equation
rho_N(lambdaOperation n f)=operation n (rho_N f) for all n,N, including N=0.
Using the jointly injective finite specializations, prove every PreLambdaRing
and SpecialLambdaRing law for these operations. Package the instances and
prove lambda_n(e_1)=e_n for every natural n. Provide preserving finite
specialization maps to the actual finite polynomial special lambda rings.

## Pre-proof review

This operates only on the integral symmetric-function ring. It does not give
an arbitrary coefficient ring a lambda structure. It uses the existing bounded
stable realization without changing the polynomial-backed foundational type.
One bound works simultaneously for all alphabet sizes after each operation.
The special laws are descended from the already proved finite signed-coefficient
laws, not from their positive special cases. Finite compatibility includes
small alphabets below the stable range and the empty alphabet. Index zero gives
lambda_0=1 and hence agrees with e_0=1 in the generator theorem.

## Proof and validation plan

Establish symmetry, zeroLast compatibility, and boundedness before constructing
operations. Then prove pointwise specialization, use joint injectivity for all
class laws, and compute on e_1 through the finite sum of variables. Review the
elaborated main declarations independently, test index zero/empty alphabet,
run full builds and transitive axiom audit, update status and commit.

No LSTABLE declarations are accepted at this initial handoff.

## Exported declarations and separate final review

`isSymmetric_operation`, `zeroLast_operation`, `lambdaFamily`, its component
formula and `lambdaFamily_degree_bound`; `lambdaOperation` and
`lambdaOperation_mem_degreeLE`; `rhoPolynomial`,
`rhoPolynomial_lambdaOperation`, `eq_of_rhoPolynomial_eq`;
zero/one/addition/unit/product/iteration laws; actual PreLambdaRing and
SpecialLambdaRing instances on SymmetricFunction Z; `rhoLambdaHom` and its
underlying specialization formula; `lambda_e_one` for all natural indices.

The same worker separately reviewed all elaborated main types in
`.scratch/LStableReview.lean`. The input type is the bounded stable subtype,
not an unrestricted product. The bound theorem has one d for every N, and
produces n*d uniformly. The transported degree filtration is the existing
weighted elementary-generator filtration. Specializations preserve the exact
operation for all N, without a stable-range lower bound. The generator theorem
includes n=0. Only the integral source gets these instances; no general
coefficient ring is presumed to be a lambda ring. The two special fields use
the fixed LPOLY polynomials and hold for all source elements and all n,m.
Examples cover lambda_0(e_1) and operation compatibility at the empty alphabet.

## Validation and completion

Exact checked state: the completion commit containing this handoff.
- `python3 scripts/check_project.py`: exit 0; all 50 accepted modules built,
  root coverage verified, 955 declarations passed the transitive axiom audit.
- `python3 scripts/test_check_project.py`: exit 0; five tests passed.
- `lake env lean .scratch/LStableReview.lean`: exit 0; statement review,
  special-instance synthesis, and direct generator/iteration axiom checks.
- Lean MCP final Structure diagnostics: empty; `git diff --check`: exit 0.
- Dependency pins and original colleague checkouts unchanged.

All LSTABLE acceptance criteria pass. LFREE is ready. The free-object theorem
for arbitrary special lambda targets, including torsion, and RELEASE remain.
An initial degree-bound proof timed out while inferring a nested subtype;
explicit finite specialization and family arguments resolve it without raising
heartbeats or altering the mathematical statement.
