# The standard symmetric-function Hopf algebra

- Task: HOPF; owner: Codex (single worker); status: done.
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

Initial pre-proof status: all HOPF implementation and validation pending. A Hopf instance alone will not
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

## Series substep: statement review before proof search

The auxiliary series have coefficients in the already constructed bounded ring;
they do not redefine symmetric functions or assert a completed realization.
`elementaryGeneratingSeries = PowerSeries.mk e` and
`completeGeneratingSeries = PowerSeries.mk h` satisfy
`rescale (-1) elementaryGeneratingSeries * completeGeneratingSeries = 1`.
For the two canonical inclusions `ι₁, ι₂ : SF R →ₐ[R] SF R ⊗[R] SF R`, prove
`map Δ E = map ι₁ E * map ι₂ E` and then the same equality for H by uniqueness
of an inverse. Taking coefficients yields the required `Δ(h n)` formula.
This argument uses inverse uniqueness in a commutative ring, with no division
by an integer or hypothesis on characteristic. Positive Newton primitivity
will use formal derivatives and the integral Newton identity, not cancellation
of the integer index.

## Total grading substep: reviewed declarations

Define `tensorDegree R d` as the R-span of tensors `f ⊗ g` for which there
exist natural i,j with i+j=d, f homogeneous of degree i and g homogeneous of
degree j. Prove products of elements in tensorDegree i and tensorDegree j
belong to tensorDegree (i+j). Prove that `comultiplication f` belongs to
`tensorDegree R d` whenever f is homogeneous of degree d. This is the total
tensor grading, with both factor degrees counted. Construct
`degreeZeroEquiv R : R ≃ₗ[R] homogeneousSubmodule R 0` using the coefficient
map and counit. Together with GRADE's existing direct-sum decomposition this
expresses connectedness. Also prove the antipode preserves each homogeneous
piece. All conclusions retain arbitrary CommRing R, including the zero ring.

## Checkpoint 2: complete coproduct and primitive power sums

`Hopf/Series.lean` exports the E/H generating series, their inverse identity,
`comultiplication_elementarySeries`, `comultiplication_completeSeries`, and
`comultiplication_h`. `Hopf/Primitive.lean` exports `newton_convolution`, the
positive-index `powerSumGeneratingSeries`, its integral logarithmic-derivative
identity, and `comultiplication_p`. The proof uses a formal derivative only as
a derivation; it never infers equality from equality of derivatives or divides
by an index. Thus torsion and zero coefficient rings remain included.

Validation: `python3 scripts/check_project.py` passed for all 23 accepted modules
and audited 513 declarations. Lean MCP diagnostics for Primitive were empty.
Separate `#check @...` review confirms both coproduct statements have only
CommRing hypotheses, h has all natural indices, and p has positive indices.
Direct axiom checks for both results use only standard Lean foundations.
The exact checked sources are in the commit containing this entry. HOPF remains
in progress: total grading/connectedness and finite alphabet addition remain.

## Finite alphabet substep: reviewed contract

For finite sets of variables σ and τ, define specialization to either alphabet
by elementary evaluation. The tensor specialization sends f⊗g to the product
of their specializations renamed into the disjoint alphabet σ⊕τ. Prove its
composition with Δ equals elementary specialization to σ⊕τ, and identify the
single-alphabet specialization with the existing `rho R N` when σ=Fin N.
Prove the finite elementary antidiagonal identity from the product of the two
finite generating series. This is ordinary alphabet addition and requires no
lambda structure on coefficients or tensors.


## Final interface, separate statement review, and completion

`Hopf/Grading.lean` exports `tensorDegree`, `tmul_mem_tensorDegree`, its graded
multiplication structure, `comultiplication_mem_tensorDegree`, `degreeZeroEquiv`,
`counit_eq_coeff_zero`, `counit_eq_zero_of_homogeneous`, and
`IsHomogeneous.antipode`. The span defining tensorDegree counts BOTH factor
degrees. GRADE already supplies the direct-sum grading on SF R. The counit is
zero on positive pieces and inverse to coefficient inclusion on degree zero.

`Hopf/Alphabets.lean` exports `SymmetricFunctions.esymm_sum_alphabet`,
`alphabetSpecialization`, its `e` and `fin` formulas,
`tensorAlphabetSpecialization`, its pure-tensor formula, and the algebra-map
identity `tensorAlphabetSpecialization_comp_comultiplication` with pointwise
version. The alphabets are arbitrary finite types, including empty types.
Their sum is disjoint union. The tensor base is exactly R. No lambda structure
on R or on the tensor product is asserted.

The implementing worker made a separate review of the fully elaborated types
in `.scratch/HopfFinalReview.lean`, apart from the proofs. It confirms the
indices, degree sum, explicit associators, coefficient-map tensor bases, and
absence of Nontrivial, characteristic, torsion-free, or flatness assumptions.
Mathlib HopfAlgebra and cocommutativity instances also synthesize for PUnit.
The earlier public-type-irreducible examples check Δ(e 2) including its middle
term and S(e 2)=e 1²-e 2. No contract changes were required.

Final validation (exact sources are the commit containing this completion):
- `python3 scripts/check_project.py`: exit 0; 25 accepted modules, 547 declarations
  passed the transitive axiom audit. All affected modules/root built cleanly.
- `python3 scripts/test_check_project.py`: all five tests passed.
- `lake env lean .scratch/HopfFinalReview.lean`: exit 0.
- Lean MCP final Grading/Alphabets diagnostics: empty.
- `git diff --check`: passed. All new files covered by the root and registry.

All HOPF criteria and the roadmap's finite alphabet-addition interpretation are
proved. LPOLY is the next ready core task. The lambda-ring milestones and RELEASE
remain open. The pinned dependencies and original colleague checkouts are unchanged.

Useful implementation notes: a natural successor used as a positive index in a
finite sum should use `Nat.succPNat`; raw subtype constructors can trigger
semireducibility mismatches in rewrites. Explicit degrees in the graded tensor
unit proof avoid expensive metavariable searches. The finite alphabet proof
cancels only a power of the unit -1, never an integer index.
