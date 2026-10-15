# Integral plethysm and alphabet operations

- Task: PLETH; owner: Codex (integral notation foundation only); status: in_progress.
- Prerequisites: LFREE a71e8ee, NEWTON fde87d5, HOPF 00cc4cf.
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- Current authorized scope: `SymmetricFunctions/Plethysm/Integral.lean`, sufficient
  to support the user's notation/readability request. Full extension not claimed.

## Reviewed foundational contract

`plethysm (f g : SymmetricFunction Z) : SymmetricFunction Z := lambdaEval g f`.
Prove both identities with e_1, associativity, and evaluation of e_n as lambda_n.
The operation is a ring morphism and a lambda morphism in its outer argument.
It is not asserted additive in the inner argument. Only integer coefficients
are used, and the actual constructed special structure is used on the source.
The proof of associativity is the already proved naturality of lambdaEval.

## Remaining full-task obligations

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
