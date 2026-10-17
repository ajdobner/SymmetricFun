# Exterior powers on integer polynomial rings

- Task: LLINE; owner: Codex (single worker); status: done.
- Prerequisite: LDEFS 0bdf4df.
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- Scope: LambdaRing/Polynomial/{SeriesUnits,Operations,Naturality,Degree}.lean.
- Search/reuse: pinned PowerSeries.invOfUnit, Units.zpow, Finsupp.prod_add_index',
  MvPolynomial coefficient Finsupp and finite monomial decomposition. No copied
  colleague code. There is no existing lambda-ring structure in pinned Mathlib.

## Mathematical contract and proposed declarations

For any variable type sigma (in particular every finite alphabet), let m_d be
its monomial with coefficient one. Define `lineUnit a` with underlying series
1+C(a)u and inverse from PowerSeries.invOfUnit. Define `totalUnit f` as the finite
product over coefficient support of `(lineUnit m_d)^(coeff f d : Int)`.
`operation k f` is its kth coefficient. Prove operation_0=1, operation_1 f=f,
addition convolution, unit normalization, and `totalUnit (-f)=(totalUnit f)^-1`.
Give explicit negative-monomial formulas and the inverse convolution law.
Package only PreLambdaRing at this stage.

Prove compatibility with substitutions carrying each variable to either zero
or a coefficient-one monomial. This includes arbitrary renaming and setting
variables to zero (and hence finite alphabet transitions). A general ring
substitution need not preserve these operations and will not be claimed.
For f.totalDegree <= d prove `(operation k f).totalDegree <= k*d` for all k,d.
The zero polynomial and degree zero are included; negative coefficients do
not invalidate the bound because the kth coefficient uses only total monomial
multiplicity k. No completion of symmetric functions is introduced: formal
series merely encode operations and each coefficient is a finite polynomial.

## Pre-proof review

The integers in the exponent are signed coefficient values, not natural
multiplicities; inverse units are essential. The construction is integral,
with no rational division or torsion-free target claim. The finite-degree
bound is ordinary degree in the alphabet variables here, compatible with the
weighted elementary-generator degree via FINITE. Finiteness is polynomial
support, so the operations can be defined even for infinite variable types.
No universal special identity is assumed or concluded in LLINE. Proof of
specialness for virtual differences remains exactly LSPECIAL's contract.

## Proof strategy and validation plan

First prove generic identities for line units and coefficients of normalized
units. Use coefficient Finsupp addition to prove totalUnit multiplicativity
under polynomial addition; coefficient one reconstructs f. Prove substitution
by polynomial additive generation and monomial preservation. Prove the degree
bound using closure of coefficientwise bounds under products and inverses,
or equivalent explicit coefficients of integer powers. Review elaborated
interfaces independently, check convention examples, then run full builds,
MCP diagnostics, transitive axiom audit, and checker tests.

No LLINE implementation is accepted at this initial handoff.

## Implemented declarations

- SeriesUnits: `lineUnit`, coefficient and map formulas, normalization under
  inverse and integer powers, `coeff_one_unit_inv/zpow`, `coe_lineUnit_inv`,
  `coeff_lineUnit_inv`, and `coeff_lineUnit_negSucc`. The last gives the full
  integral binomial formula (-a)^n * choose(r+n,r) for multiplicity -(r+1).
- Operations: `totalUnit`, `operation`, additive hom `totalUnitHom`,
  `totalUnit_add/neg/sub/zsmul`, `totalUnit_monomial/one`, coefficient-zero and
  coefficient-one identities, addition convolution, the PreLambdaRing instance,
  `operation_unit`, negative monomial formulas and inverse convolution.
- Naturality: `IsLineMonomial` (zero or coefficient-one monomial), closure under
  products and powers, `IsMonomialSubstitution`, `totalUnit_natural`,
  `operation_natural`, preserving `monomialHom`, `operation_rename` (even
  noninjective renaming), and `operation_setZero` for any variable predicate.
- Degree: `CoefficientBound` and closure under multiplication, powers and finite
  products; bounds for both signs of line multiplicity; `coefficientBound_totalUnit`,
  `operation_totalDegree_le`, and `operation_totalDegree`.

## Separate final statement review

Codex read the fully elaborated statements in `.scratch/LLineReview.lean`
independently of their proofs. The ambient variable type is arbitrary, so all
finite alphabets are included. Signed exponents are actual integer exponents
of units. Negative coefficients are never converted to natural numbers.
The degree statement quantifies over all k,d and all integer polynomials f,
assuming only totalDegree f <= d; no positivity hypothesis occurs.
Naturality requires precisely that variable images be zero or coefficient-one
monomials, and imposes no injectivity condition on the substitution. The unit
normalization is exterior-power (1+t). Only PreLambdaRing is instantiated;
no SpecialLambdaRing instance or product/iteration identity is claimed here.
Examples check the second exterior power of a negative monomial and of 1.

## Validation and completion

Exact checked state: the commit containing this completion handoff.
- `python3 scripts/check_project.py`: exit 0; all 44 accepted modules built,
  root coverage verified, 864 declarations passed the transitive axiom audit.
- `python3 scripts/test_check_project.py`: exit 0; all five tests passed.
- `lake env lean .scratch/LLineReview.lean`: exit 0; explicit axiom checks of
  naturality and the degree theorem use only allowed standard foundations.
- Lean MCP final SeriesUnits, Operations, Naturality, Degree diagnostics: empty.
- `git diff --check`: exit 0. No dependency pin changes or colleague checkout edits.

All LLINE acceptance criteria pass. LSPECIAL is ready. Its remaining work is
both special identities for arbitrary signed integer coefficients, before any
special instance can be packaged or transported to stable symmetric functions.
