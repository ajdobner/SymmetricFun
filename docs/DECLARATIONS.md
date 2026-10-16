# Symmetric functions: declaration guide

Import `SymmetricFunctions` for the accepted library. The generated
[complete declaration index](declarations.tsv) records 1,092 noninternal
declarations, their defining modules, and their kinds. It includes generated
class declarations; private helpers and anonymous examples are omitted. The
axiom audit also covers those omitted declarations (1,448 declarations total).

Regenerate the index after building the library:

```sh
lake build
lake env lean scripts/DeclarationIndex.lean
```

The [release review script](../scripts/ReviewRelease.lean) prints the elaborated
major contracts, their referenced definitions, and representative axiom
dependencies. Run it with `lake env lean scripts/ReviewRelease.lean`.
The [release handoff](handoffs/RELEASE.md) records the separate mathematical
review and initial validation. The [notation handoff](handoffs/NOTATION.md)
records the subsequent readability work. The [lambda simplification repair](handoffs/LSIMP.md) records the public normal-form policy. The latest extension validation is recorded in the [RATIONAL handoff](handoffs/RATIONAL.md).

## Optional notation and descriptive aliases

Import `SymmetricFunctions.Notation` and activate `open scoped SymmetricFunctionNotation` for `Λ[R]`, `ω f`, `λ[n] a`, and integral `f⟦g⟧`. The [notation guide](NOTATION.md) maps every symbol to its declaration and records precedence and alphabet/coefficient conventions. `Names.lean` supplies `elementary`, `complete`, `powerSum`, and `elementaryCompleteInvolution` as aliases without changing e/h/p/omega callers.

[Integral plethysm](../SymmetricFunctions/Plethysm/Integral.lean) exports `plethysm`, `plethysm_e`, both e_1 identity laws, `plethysm_assoc`, `add_plethysm`, `mul_plethysm`, and `lambda_plethysm`. Both operands have integer coefficients. [Adams](../SymmetricFunctions/Plethysm/Adams.lean) proves `plethysm_p`,
`adams_p`, composition, and finite-variable expansion, integrally.
[TensorProduct](../LambdaRing/TensorProduct.lean) constructs the actual integral
tensor special lambda structure; [Alphabets](../SymmetricFunctions/Plethysm/Alphabets.lean)
proves `comultiplicationLambdaHom` and `comultiplication_plethysm`. PLETH is complete;
see its [handoff](handoffs/PLETH.md) and `scripts/ReviewPlethysm.lean`.

## Polynomial foundation and classical generators

Unless indicated otherwise, the namespace is `SymmetricFunction`.

| Module | Entry points | Contract |
| --- | --- | --- |
| [Basic](../SymmetricFunctions/Basic.lean) | `SymmetricFunction`, `polynomialEquiv`, `e`, `eval`, `eval₂`, `ringHom_ext`, `induction_on` | Dedicated polynomial-backed type with positive internal elementary indices; public `e 0 = 1`; universal evaluation and public generator reasoning. |
| [Partition](../SymmetricFunctions/Partition.lean) | `SymmetricFunctions.Partition.exponentEquiv` | Mathlib `Nat.Partition d` corresponds to positive-index exponent vectors of weighted degree `d`. |
| [Grading](../SymmetricFunctions/Grading.lean) | `IsHomogeneous`, `homogeneousSubmodule`, `decompose`, `degreeLE`, `exists_mem_degreeLE` | Weight of `e n` is `n`; direct-sum grading and exhaustive degree filtration. |
| [Elementary basis](../SymmetricFunctions/Basis/Elementary.lean) | `ePart`, `eBasis`, `eBasisAll` | Partition bases of homogeneous pieces and the whole ring. |
| [Monomial basis](../SymmetricFunctions/Basis/Monomial.lean) | `mPart`, `rho_mPart`, `coeff_rho_mPart`, `mBasis`, `mBasisAll`, `mBasis_repr_eq_coeff` | Actual stable lifts of Mathlib finite orbit sums, partition bases, and representative-independent finite coefficients over arbitrary rings. |
| [Base change](../SymmetricFunctions/BaseChange.lean) | `map`, `baseChange` | Coefficient functoriality and `A ⊗[ℤ] SymmetricFunction ℤ ≃ₐ[A] SymmetricFunction A`. |
| [Complete](../SymmetricFunctions/Complete.lean) | `h`, `h_zero`, `h_two` | Integral recurrence with `E(-t)H(t)=1` and `h 0 = 1`. |
| [Omega](../SymmetricFunctions/Omega.lean) | `omega`, `omega_omega` | Grading-preserving elementary/complete involution. |
| [Complete basis](../SymmetricFunctions/Basis/Complete.lean) | `hBasis`, `hBasisAll` | Complete partition bases and polynomial freeness. |
| [Power sums](../SymmetricFunctions/PowerSum.lean) | `p`, `p_two` | Positive-index integral Newton power sums and finite specialization. |

## Rational evaluation and independent alphabets

These interfaces require `[CommRing R] [Algebra ℚ R]`. They do not assign lambda
operations to R, and they do not alter integral freeness for torsion targets.

| Module | Entry points | Contract |
| --- | --- | --- |
| [Rational presentation](../SymmetricFunctions/Plethysm/Rational.lean) | `powerSumPolynomialEquiv`, `powerSumChangeOfGenerators`, `powerSumHomogeneous` | Proved algebra equivalence `MvPolynomial ℕ+ R ≃ₐ[R] SymmetricFunction R` sending X_k to p_k; both inverse Newton substitutions preserve weighted degree. No Nontrivial assumption. |
| [Power-sum basis](../SymmetricFunctions/Basis/PowerSum.lean) | `pPart`, `pBasis`, `pBasisAll`, `pBasisAll_repr` | Actual products of power sums give homogeneous and whole-ring partition bases. The products themselves are defined over every commutative ring. |
| [Universal evaluator](../SymmetricFunctions/Plethysm/Rational.lean) | `powerSumEval`, `powerSumEvalEquiv`, `algHom_ext_p` | Specify every positive power-sum image in any commutative R-algebra. The unique R-algebra map fixes outer coefficients; no target lambda structure is required. |
| [Alphabet operations](../SymmetricFunctions/Alphabets.lean) | `negativeAlphabetEval`, `scaledAlphabetEval`, `sumAlphabetEval`, `productAlphabetEval`, `powerSumAdams` | Virtual minus negates every p-image; scaling by t multiplies the kth image by t^k. Adams raises actual finite alphabet variables to powers. |
| [Tensor and mixed objects](../SymmetricFunctions/Alphabets.lean) | `tensorPowerSumPolynomialEquiv`, `tensorAlphabetEval`, `MixedAlphabet`, `mixedPowerSumPolynomialEquiv`, `mixedAlphabetEval`, `mixedAdams`, `mixedPlethysticEval` | Independent tensor factors with explicit generator maps and universal evaluation. Inner polynomial parameters receive Adams powers, while R-coefficients remain fixed. |
| [Geometric alphabets](../SymmetricFunctions/Alphabets.lean) | `geometricAlphabetEval`, `geometricAlphabetEval_denominator`, `geometricAlphabetEval_unique`, `geometricAlphabetEval_p_field` | X/(1-t) evaluation requires every positive-index 1-t^k to be a unit. Denominator equations characterize it; the field formula is p_k[X]/(1-t^k). No infinite-series evaluation is asserted. |

[Examples/Rational](../SymmetricFunctions/Examples/Rational.lean) checks repeated
parts, degree zero, the zero ring, even virtual negation, formal scaling, fixed
outer coefficients, transforming inner parameters, independent tensor images,
an empty polynomial alphabet, and all geometric denominators in ℚ(t).

## Stable realization

All results below assume only `CommRing R`, allowing the zero ring.

| Module | Entry points | Contract |
| --- | --- | --- |
| [Specialization](../SymmetricFunctions/Specialization.lean) | `rho`, `zeroLast`, `transition`, `transition_rho` | Elementary specialization into Mathlib's symmetric subalgebra on `Fin N`, compatible with setting the last variable to zero. |
| [Finite weighted theorem](../SymmetricFunctions/Finite/Weighted.lean) | `finitePresentation`, `liftSymmetric` | Finite fundamental theorem with weighted-degree control. |
| [Stable range](../SymmetricFunctions/Finite/StableRange.lean) | `ker_rho`, `stableRangeEquiv`, `rho_eq_iff_of_degreeLE` | Kernel generated by elementary indices above `N`; degree-at-most-`d` equivalence when `d ≤ N`. |
| [Stable families](../SymmetricFunctions/Stable.lean) | `Compatible`, `UniformlyBounded`, `BoundedStable`, `stableEquiv`, `stableEquiv_symm_eq_lift` | Algebra equivalence to compatible families satisfying **`∃ d, ∀ N, totalDegree (f N) ≤ d`**. The inverse uses any `N ≥ d` and is independent of the bound and alphabet. |

The bound is a property, not chosen mathematical data. The unrestricted inverse
limit and the degree completion are outside this realization.

## Symmetric multivariate series

[SeriesBasic](../SymmetricFunctions/Realization/SeriesBasic.lean) defines permutation
invariance and a single uniform coefficient-degree bound, both proof-irrelevant.
[PowerSeries](../SymmetricFunctions/Realization/PowerSeries.lean) exports
`toSeries`, `boundedSeriesEquiv`, `coeff_toSeries`, `finiteRestriction_toSeries`,
and `toSeries_homogeneousComponent`. The algebra equivalence uses only CommRing R.
The monomial images are actual coefficient-one exponent orbits; elementary and
complete images recover their finite polynomials for every alphabet size.
See [SERIES](handoffs/SERIES.md) for the separate statement review and validation.

## Hopf algebra

[Hopf](../SymmetricFunctions/Hopf.lean) exports the standard Mathlib
`HopfAlgebra R (SymmetricFunction R)` and cocommutativity instances, with only
`CommRing R`. The tensor base is `R`. The principal formulas are:

- `comultiplication_e`: `Δ(e n) = ∑ i+j=n, e i ⊗ e j`.
- `counit_e`: `ε(e n) = if n = 0 then 1 else 0`.
- `antipode_e`: `S(e n) = (-1)^n • h n`.
- `comultiplication_h`: the same convolution formula for complete functions.
- `comultiplication_p`: every positive power sum is primitive, integrally.
- `comultiplication_mem_tensorDegree` and `degreeZeroEquiv`: total tensor
  grading compatibility and degree-zero identification with the coefficients.

[Coefficients](../SymmetricFunctions/Hopf/Coefficients.lean) proves naturality
and integral base-change compatibility. [Alphabets](../SymmetricFunctions/Hopf/Alphabets.lean)
identifies the coproduct with addition of finite disjoint alphabets. Both
counit laws, coassociativity, both antipode laws, and cocommutativity are proved.

## Integral exterior powers and freeness

| Module | Entry points | Contract |
| --- | --- | --- |
| [Universal polynomials](../LambdaRing/UniversalPolynomials.lean) | `LambdaRing.UniversalPolynomial.productPolynomial`, `iterationPolynomial` | Independently constructed integral product/iteration polynomials, finite-alphabet evaluation, stability, weighted bounds, uniqueness, and index-zero conventions. |
| [Definitions](../LambdaRing/Defs.lean) | `PreLambdaRing`, `SpecialLambdaRing`, `LambdaRing.lambda` | Exterior convention `λ₀(a)=1`, `λ₁(a)=a`, addition convolution, unit law, and the integral product/iteration identities. |
| [Morphisms](../LambdaRing/Hom.lean) | `LambdaRingHom` | Ring morphisms preserving every exterior power, with identity, composition, and extensionality. |
| [Polynomial operations](../LambdaRing/Polynomial/Operations.lean) | `LambdaRing.Polynomial.totalUnit`, `operation` | Total series `∏ₘ (1+m t)^(aₘ)` for arbitrary signed integer coefficients. |
| [Naturality](../LambdaRing/Polynomial/Naturality.lean) and [degree](../LambdaRing/Polynomial/Degree.lean) | `operation_natural`, `operation_totalDegree_le` in `LambdaRing.Polynomial` | Monomial substitutions, including zero substitution, preserve operations; degree `d` gives degree at most `n*d` after `λₙ`. |
| [Polynomial specialness](../LambdaRing/Polynomial/Special.lean) | `LambdaRing.Polynomial.operation_mul`, `operation_iterate` | Both special identities for all signed integer polynomials; actual special instances. |
| [Stable lambda structure](../SymmetricFunctions/Lambda/Structure.lean) | `lambdaFamily`, `lambdaOperation`, `rhoLambdaHom`, `lambdaOperation_mem_degreeLE`, `lambda_e_one` | Operations transported through bounded stable families, with weighted bounds; actual integral special instance and `λₙ(e₁)=eₙ`. |
| [Preservation](../LambdaRing/Preservation.lean) | `LambdaRing.PreservesAt`, `preservingSubring` | Closure under addition, negation, multiplication and exterior powers using integral identities, valid with torsion. |
| [Universal property](../SymmetricFunctions/Lambda/Universal.lean) | `lambdaEval`, `lambdaEval_e`, `lambdaHom_ext`, `lambdaHomEquiv`, `lambdaEval_natural` | For every commutative special lambda ring `A`, `LambdaRingHom (SymmetricFunction ℤ) A ≃ A`, by evaluation at `e₁`, naturally in `A`. |
| [Surjective transport](../LambdaRing/Transport.lean) | `PreLambdaRing.ofSurjective`, `SpecialLambdaRing.ofSurjective` | Descend laws along an actually surjective ring map after proving operation preservation. |

The universal property imposes no characteristic, nontriviality, or
torsion-freeness hypothesis on `A`. Its inverse sends `e n` to `λₙ(a)` for an
arbitrary chosen `a : A`. Arbitrary coefficient rings are not assigned lambda
structures merely by being coefficient rings.

[Consolidated examples](../SymmetricFunctions/Examples.lean) check the release
conventions with the representation locally irreducible. The
[torsion example](../SymmetricFunctions/Examples/Torsion.lean) constructs a
proved special structure on `TrivSqZeroExt ℤ (ZMod 2)` and evaluates `e₁` at
a nonzero element killed by `2`; its `e₂` value is zero.

## Further work

All initial core tasks through RELEASE are complete. PLETH and MONOMIAL are
complete; RATIONAL is complete. SERIES is complete. COMPLETION is being implemented through its explicit
subtasks; SCHUR is ready by prerequisites but outside this run. BLUEPRINT and PLATFORM are
optional tooling and external-work tasks. Their exact scope and status remain
in [the registry](tasks.json). The whole symmetric-functions project is not complete.
