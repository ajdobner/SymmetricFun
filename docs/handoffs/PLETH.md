# Integral plethysm and alphabet operations

- Task: PLETH; owner: Codex (single worker); status: done. Complete implementation validated after LSIMP; historical partial checkpoint below.
- Prerequisites: LFREE a71e8ee, NEWTON fde87d5, HOPF 00cc4cf.
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- Historical notation-only scope (superseded by the completed implementation below): `SymmetricFunctions/Plethysm/Integral.lean`, sufficient
  to support the user's notation/readability request. Full extension not claimed.

## Reviewed foundational contract

`plethysm (f g : SymmetricFunction Z) : SymmetricFunction Z := lambdaEval g f`.
Prove both identities with e_1, associativity, and evaluation of e_n as lambda_n.
The operation is a ring morphism and a lambda morphism in its outer argument.
It is not asserted additive in the inner argument. Only integer coefficients
are used, and the actual constructed special structure is used on the source.
The proof of associativity is the already proved naturality of lambdaEval.

## Historical obligations at the notation-only checkpoint

Adams operations and psi_k(p_n)=p_(kn) are not yet implemented. The needed
tensor-product special lambda structure and its Hopf alphabet-addition
compatibility remain unproved. PLETH cannot be marked done after notation,
unit laws, and associativity alone. RATIONAL remains dependent on full PLETH.

## Implemented first checkpoint

`plethysm` is implemented together with `plethysm_eq_lambdaEval`, `plethysm_e`,
`e_one_plethysm`, `plethysm_e_one`, `plethysm_assoc`, `add_plethysm`,
`mul_plethysm`, and `lambda_plethysm`. The latter laws preserve multiplication,
addition, and exterior powers in the OUTER argument. The proofs reuse
lambdaEval's ring/lambda morphism laws and naturality directly.

Checked state: the NOTATION completion commit containing this handoff.
`python3 scripts/check_project.py` passes for 59 modules and 1,067 transitive
axiom checks. The direct associativity and lambda-preservation audits use only
propext, Classical.choice, and Quot.sound. Separate elaborated-statement review
confirms integer coefficients, outer/inner argument order, and both unit laws.
Precedence and nested notation examples are in Examples/Notation; see the
NOTATION handoff for their detailed validation.

No current proof goal is left open in the implemented module. The next concrete
PLETH step is to review and implement Adams operations with their integral
power-sum formulas, before undertaking tensor-product lambda structure and
Hopf compatibility. These remaining obligations were not part of the requested
notation pass and were not weakened or marked complete.

## Full implementation resumed after LSIMP 9aa493d

The user now authorizes the entire PLETH contract, followed by MONOMIAL and
RATIONAL. The earlier scope limit above describes only checkpoint 949463c.
The active source retains the convention f[g]=lambdaEval g f and its proved
unit/associativity laws.

### Adams contract, reviewed before proof search

For positive k, define `adams k : LambdaRingHom (SymmetricFunction Z)
(SymmetricFunction Z)` as lambdaEval (p k). Thus initially adams k f=f[p_k].
Prove every finite specialization equals `MvPolynomial.expand k (rho_N f)`.
The expansion substitutes x_i^k for each actual finite alphabet variable and
fixes integer coefficients. It is a monomial substitution and hence preserves
the actual polynomial exterior powers. Both maps out of SF Z preserve lambda;
e_1 extensionality identifies them using rho(p_k)=sum x_i^k.

Deduce `adams k (p n)=p (k*n)`, identity at k=1, composition at k*l, and the
corresponding power-sum plethysms. Establish also the usual left power-sum
description p_k[f]=adams k f from the integral Newton/total-series identities;
this must not cancel a nonunit integer or restrict general special targets.
Where a general special target is used, retain all torsion-target generality.

### Tensor contract and strategy, reviewed before proof search

The tensor needed for Hopf alphabet addition is
T = SF Z tensor[Z] SF Z. Construct an actual SpecialLambdaRing T such that
both canonical tensor inclusions preserve all exterior powers. Prove the
existing coproduct Delta is a LambdaRingHom, with Delta(e_1)=e_1 tensor 1 +
1 tensor e_1, then obtain the alphabet-addition evaluator identity for every
outer symmetric function. Integer scalars and the tensor base must remain Z.
The existing arbitrary-CommRing Hopf results are unchanged.

Embed T injectively into the product of finite disjoint-alphabet polynomial
rings using the proved two-block elementary injectivity and polynomial tensor
presentation. The product carries pointwise actual special operations.
Show the image is closed under all exterior powers: both factor images are
closed by finite lambda preservation, products by the integral product identity,
sums by convolution, and negatives by inverse-series coefficient recurrence.
Transport the restricted structure back along the proved embedding. This proves
the necessary tensor structure without confusing elementary polynomial variables
with line elements. Generic product/subring transport helpers retain arbitrary
special rings, including torsion. No generic tensor-lambda theorem is assumed.

Validation follows the exact task criteria, with separate elaborated-statement
review, root examples, full builds and transitive axioms at coherent substeps.
PLETH remains in progress until Adams and tensor compatibility both pass.

### Intermediate interfaces

`LambdaRing.piPreLambdaRing` and `piSpecialLambdaRing` use pointwise operations
on any family of arbitrary special commutative rings. Evaluation at a coordinate
is `evaluationHom`. `PreLambdaRing.ofInjective` and
`SpecialLambdaRing.ofInjective` reflect the respective laws through a proved
injective ring map that intertwines the specified operations. They do not
assert a lambda structure for an arbitrary ring map.

`LambdaRing.lambdaStableSubring S` consists exactly of those a for which every
lambda_n(a) lies in S. The integral special identities prove subring closure
and closure under exterior powers; the n=1 identity proves this is a subring
of S. No assumptions about integer cancellation are used.

The next tensor-specialization interface is over every CommRing R:
`tensorPolynomialEquiv R : (SF R tensor[R] SF R) ≃ₐ[R]
MvPolynomial (PNat + PNat) R`, and
`eq_of_tensorAlphabetSpecialization_eq`: equality of the specializations in
all pairs (Fin N, Fin M) implies equality of tensors. This is an algebraic
presentation only, with no line-element lambda interpretation. Its injectivity
proof uses the existing two-block bounded elementary substitution theorem and
a finite bound on both polynomials' variable indices.

## Completed implementation and statement-only review

The implementing worker ran `scripts/ReviewPlethysm.lean` after the proofs were
finished, then reviewed the printed definitions and fully elaborated theorem
types independently of their proof bodies. Plethysm has exactly f[g]=lambdaEval g f
and integer coefficients. `adams k` is a genuine LambdaRingHom, with positive
index k, and `plethysm_p` proves p_k[f]=f[p_k]. `rhoPolynomial_adams` raises
finite alphabet variables, not elementary-generator variables. `adams_p`,
`adams_one`, `adams_comp`, and `adams_adams` give index multiplication and
composition integrally. `lambdaEval_p_polynomial` holds for arbitrary signed
integer polynomials and any variable type. `plethysm_p_neg` is virtual negation,
with a minus sign for every positive index, including even indices.

The tensor structure is the necessary integral square SF Z tensor[Z] SF Z.
Its operations are proved to exist using lambda closure of the image in all
finite disjoint alphabets. Injectivity proves the chosen lifts are determined
uniquely and reflects all special identities. Both factor inclusions are actual
lambda morphisms. `comultiplication_eq_lambdaEval` identifies the existing Hopf
map with evaluation at e_1 tensor 1 + 1 tensor e_1;
`comultiplicationLambdaHom`, `comultiplication_lambda`, and
`comultiplication_plethysm` prove the required compatibility. No generic tensor
structure is silently assumed. The algebra presentation and joint finite
specialization injectivity retain arbitrary CommRing coefficients. All generic
closure/transport lemmas allow torsion. Existing arbitrary-ring Hopf structures
and torsion-target freeness remain unchanged.

### Exported modules

- Plethysm/Adams: `LambdaRing.Polynomial.expandHom`; `adams`,
  `rhoPolynomial_adams`, `adams_e_one`, `adams_p`, `adams_one`, `adams_comp`,
  `adams_adams`, `plethysm_p_p`, `lambdaEval_p_polynomial`, `plethysm_p`,
  `plethysm_p_neg` and evaluation bridges.
- Hopf/TensorSpecialization: `tensorPolynomialEquiv`, generator formulas,
  `tensorAlphabetSpecialization_eq_aeval`, `eq_of_tensorAlphabetSpecialization_eq`.
- LambdaRing/Pi and Subring: pointwise instances and `evaluationHom`,
  `int_aeval_mem`, `lambdaStableSubring`, membership/closure lemmas.
- LambdaRing/Transport: injective reflection of pre-lambda and special laws.
- LambdaRing/TensorProduct: `tensorAlphabetEmbedding` and injectivity,
  `lambda_mem_range_tensorAlphabetEmbedding`, `tensorLambdaOperation`, actual
  pre-lambda/special instances, `tensorAlphabetSpecialization_lambda`,
  `lambda_tmul_one`, `lambda_one_tmul`, both inclusion lambda homomorphisms.
- Plethysm/Alphabets: coproduct evaluator identity and preserving homomorphism,
  exterior-power and plethysm compatibility.

### Validation and provenance

- `python3 scripts/check_project.py`: exit 0; 66 accepted modules, root coverage,
  1,154 transitive axiom checks, notation and public-lambda simp regressions.
- `lake env lean scripts/ReviewPlethysm.lean`: exit 0. Representative Adams,
  tensor specialness and Hopf-plethysm declarations use only propext,
  Classical.choice and Quot.sound. Arbitrary-ring Hopf and actual torsion-target
  SpecialLambdaRing instances still synthesize.
- `lake env lean scripts/DeclarationIndex.lean`: exit 0, 874 public/noninternal
  declarations indexed. Lean MCP tensor and example diagnostics: clean.
- Examples exercise nested plethysm, indices 2 and 3, even virtual negation,
  signed finite polynomials, tensor index zero, the degree-two cross term,
  and empty finite alphabets. `git diff --check`: passed.
- Reused pinned Mathlib polynomial expansion, tensor algebra equivalences and
  existing local integral identities; no new colleague code copied. Pins and
  original reference checkouts unchanged.

Checked principal source SHA-256 hashes:
Adams `53959de5b88559d4176a65fde98149d94dc3eb117d22e09b4dff0ed5a70af54e`;
TensorProduct `defeb66bd53f6616228bb499811a1ca2670a8c8e0ea1fa6629f1b6fd7075edf3`;
Alphabets `f20d5c4bc6adae7f2a9ca932e080b532cba951c2d811fa27e2cf07b665340066`.
All PLETH acceptance criteria pass. MONOMIAL and RATIONAL are ready; MONOMIAL
is next in this unattended run. They remain separate incomplete milestones.
