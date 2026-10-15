# The standard symmetric-function Hopf algebra

- Task: HOPF; owner: Codex (single worker); status: in_progress.
- Prerequisites: OMEGA ce87705, NEWTON fde87d5, BASE 9a38147, GRADE fc48b62.
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- Scope: SymmetricFunctions/Hopf.lean and supporting Hopf modules if needed.
- References: pinned Bialgebra.ofAlgHom, HopfAlgebra.ofAlgHom, tensor associator,
  graded tensor and formal power-series APIs. No colleague code copied.

## Mathematical contract and proposed interface

For every CommRing R define algebra maps on the public algebra:
- comultiplication e n = ∑ (i,j) in antidiagonal n, e i ⊗[R] e j;
- counit e n = 0 for n>0 (and counit 1=1);
- antipode e n = (-1 : R)^n • h n, including n=0.
Prove coassociativity using the tensor associator over R, both counit laws,
and both convolution antipode laws. Instantiate Mathlib HopfAlgebra R.
Prove cocommutativity, comultiplication h n = ∑ h i⊗h j, and each positive
p n primitive. Prove the grading is connected and comultiplication respects
total tensor degree, and prove compatibility with arbitrary coefficient maps.

The tensor degree-d submodule will be the sum over i+j=d of the images of
homogeneous degree-i/degree-j pure tensors; degree-zero connectedness identifies
the zero piece with the coefficient ring. Coefficient compatibility must address
the change of tensor base explicitly, not silently compare R- and S-tensors.

## Pre-proof statement review

Elementary generators are divided-power-like under comultiplication, not
primitive; in particular Δ(e 2) has e 1⊗e 1. The antipode uses complete functions
and the sign on their full index. All maps have the stated algebra/linear
structures and tensor base R. No division, Nontrivial, characteristic-zero,
flatness, or torsion-free assumptions are allowed. Ring/Hopf results are not
lambda structures. No mathematical contract changes are needed.

## Strategy and acceptance tracking

Construct the maps by public elementary evaluation. Reduce equality of algebra
maps to generators. Use antidiagonal associativity, endpoint sums, and COMPLETE's
four convolution identities. Register Mathlib structures only after their laws
are proved. Use integral formal-series identities for complete coproduct and
primitive p; prove the grading and coefficient naturality separately.

Pending: all HOPF implementation and validation. A Hopf instance alone will not
mark this task done; all additional acceptance statements above remain required.

## Checkpoint 1: Hopf instance and coefficient naturality

Implemented `Hopf/Basic.lean`: `comultiplication`, `counit`, `antipode`, their
all-natural-index elementary formulas, coassociativity with explicit tensor
associator, both counit and antipode laws, and cocommutativity. These laws build
actual Mathlib `Bialgebra`, `HopfAlgebra`, and `Coalgebra.IsCocomm` instances.
The degree-two examples include the middle coproduct term and the antipode sign.

Implemented `Hopf/Coefficients.lean`: `map_h`, the heterobasic `tensorMap` using
Mathlib `Algebra.TensorProduct.mapRingHom`, naturality of all three Hopf maps,
and compatibility with the integral `baseChange` equivalence on pure tensors.
No extra assumptions on either coefficient ring. An explicit integer annotation
in `counit_baseChange` prevents confusing integral evaluation with evaluation in R.

Validation of this checkpoint: `python3 scripts/check_project.py` passed with
21 accepted modules and all 484 declarations audited. Lean MCP diagnostics for
Coefficients were empty. Separate elaborated-type review in the scratch
`HopfReview.lean` and `HopfCoefficientsReview.lean` confirms arbitrary CommRing R/S,
positive/public index conventions, and the changed tensor base. The reviewed
source state is the commit containing this entry. Dependencies are unchanged.

Remaining required work: complete-function coproduct, integral primitivity of
positive power sums, connected total grading, and finite alphabet-addition
interpretation. This checkpoint does not complete HOPF.
