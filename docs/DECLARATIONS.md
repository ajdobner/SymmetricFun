# Symmetric functions: declaration guide

Import `SymmetricFunctions` for the accepted library. The generated
[complete declaration index](declarations.tsv) records 1,453 noninternal
declarations, their defining modules, and their kinds. It includes generated
class declarations; private helpers and anonymous examples are omitted. The
axiom audit also covers those omitted declarations (2,021 declarations total).

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
records the subsequent readability work. The [lambda simplification repair](handoffs/LSIMP.md) records the public normal-form policy. The latest extension validation and parent contract review are recorded in the
[COMPLETION handoff](handoffs/COMPLETION.md).

## Optional notation and descriptive aliases

Import `SymmetricFunctions.Notation` and activate `open scoped SymmetricFunctionNotation` for `Λ[R]`, `ω f`, `λ[n] a`, integral `f⟦g⟧`, and completed `Ω`. The [notation guide](NOTATION.md) maps every symbol to its declaration and records precedence and alphabet/coefficient conventions. `Names.lean` supplies `elementary`, `complete`, `powerSum`, and `elementaryCompleteInvolution` as aliases without changing e/h/p/omega callers.

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

## Degree completion

[Graded completion](../SymmetricFunctions/Completion/Graded.lean) constructs a
product of graded pieces with finite antidiagonal multiplication. Its generic
`GradedCompletion.map` extends degree-preserving algebra maps.
[Symmetric completion](../SymmetricFunctions/Completion/Basic.lean) specializes
to weighted homogeneous pieces, provides `completionEmbedding` with injectivity,
and `DegreeCompletion.truncate` with component and product compatibility.
The cutoff is inclusive; no uniform degree bound is imposed on completed elements.
See [COMP-ALG](handoffs/COMP-ALG.md) for the statement review and validation.
[Completed realization](../SymmetricFunctions/Completion/Realization.lean)
exports `completionSeriesEquiv` with all symmetric MvPowerSeries ℕ R, without a
uniform bound. `completionToSeries_component` identifies homogeneous layers;
`completionToSeries_embedding` and `completedFiniteSpecialization_embedding`
preserve the bounded and finite-alphabet realizations. Completed finite
specialization takes values in formal power series, not necessarily polynomials.

[Completed Omega](../SymmetricFunctions/Completion/Omega.lean) defines
`completeSeries`, `elementarySeries`, `signedElementarySeries` and
`signedCompleteSeries`. Both signed generating identities hold in either order.
`completeSeriesUnit` exhibits Ω as a unit. Finite specialization commutes with
degree projections and sends Ω's nth layer to the finite complete polynomial.
The opt-in `Ω` notation has completed type; `ω` retains its bounded involution.

[Certified substitution](../SymmetricFunctions/Completion/Substitution.lean)
exports `completedSubstitution` with an explicit `MvPowerSeries.HasSubst`
certificate and `completedFiniteEval` for a finite zero-constant alphabet.
The coefficient formula includes a proved finite-support assertion. Both maps
agree with bounded evaluation. Zero constants give finite-degree dependence via
`truncTotal_completedSubstitution` and `truncTotal_completedFiniteEval`.
`hasSubst_positivePowers` certifies a useful infinite alphabet;
`completedFiniteEval_complete_one_mul` evaluates Ω in one positive letter as the
inverse of 1-a. No rationality hypothesis or unrestricted infinite plethysm is used.

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

The degree-completed version lives in
[Completion/Hopf](../SymmetricFunctions/Completion/Hopf.lean).
`CompletedTensor R` is the product of total-degree pieces of the bounded tensor
algebra. `completedCoproduct_embedding` proves agreement with the original
coproduct via `tensorCompletionMap`. `completedTensorProduct F G` has component
`∑ i+j=n, F_i ⊗ G_j`, and `completedCoproduct_completeSeries` is Ω's group-like
identity in this completed target. It has no ordinary tensor-of-completions claim.

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
complete; RATIONAL, SERIES and COMPLETION are complete. The latest full audit
covers 89 accepted modules and 1,652 declarations. SCHUR is ready by prerequisites
but outside this run. BLUEPRINT and PLATFORM are
optional tooling and external-work tasks. Their exact scope and status remain
in [the registry](tasks.json). The whole symmetric-functions project is not complete.

## Schur foundations in progress

[Partition/YoungDiagram](../SymmetricFunctions/Partition/YoungDiagram.lean) exports
`Partition.rowLength`, `length`, `rowLength_eq_getElem_sort`,
`sum_rowLength_padded`, `Contained`, `contained_iff_rowLength`, and
`ofPartition_conjugate`. These use Mathlib partitions, conjugation, and Young
 diagrams directly. `FiniteTableau` is a finite-alphabet subtype of Mathlib's
semistandard tableaux; the tableau generating formula is separately unproved.
[Examples/PartitionRows](../SymmetricFunctions/Examples/PartitionRows.lean)
checks (2,1), extra zero padding, empty partitions, rows, and columns.
The [SCHUR handoff](handoffs/SCHUR.md) records the full parent contract and
subtask split; `scripts/ReviewSchur.lean` inspects accepted definitions and
statements separately from compilation. SCHUR is not yet complete.

[Schur/JacobiTrudi](../SymmetricFunctions/Schur/JacobiTrudi.lean) defines
`completeInt`, `jacobiTrudiMatrix`, and the actual determinant `schur`.
`det_jacobiTrudiMatrix` proves independence of sufficient padding;
`isHomogeneous_schur`, `map_schur`, and `rho_schur` prove weighted degree,
coefficient naturality, and finite determinant specialization. Empty and one-row
formulas are simp lemmas. [Schur/Column](../SymmetricFunctions/Schur/Column.lean)
proves `schur_indiscrete_conjugate = e` using the finite ring map
`SymmetricFunctions.upperToeplitzHom` and the h/e inverse identity. These results
assume only CommRing, with no rationality or Nontrivial hypothesis. Hall pairing, skewing and Cauchy remain subsequent subtasks.

[Schur/Triangular](../SymmetricFunctions/Schur/Triangular.lean) proves the integral
transition to the complete basis. `schurCompleteTransition_eq_delta_of_le`
specifies identity blocks ordered by `Partition.squareWeight`, the sum of squared
parts. `det_schurCompleteTransition = 1` is proved over every CommRing.
[Basis/Schur](../SymmetricFunctions/Basis/Schur.lean) exports `schurBasis` and
`schurBasisAll`, with values equal to the actual determinant `schur`.
`sum_schurBasis_repr`, `sum_schurBasisAll_repr`, and `ext_schur_coefficients`
express expansion and uniqueness. The square statistic orders the transition;
it does not change weighted degree. These basis results do not yet assert
Schur orthogonality or tableau positivity.

[Schur/Dual](../SymmetricFunctions/Schur/Dual.lean) exports `elementaryInt`,
`elementaryJacobiTrudiMatrix`, `dual_jacobiTrudi`, and `omega_schur`. The dual
formula uses the conjugate shape and any sufficient zero padding, over every
CommRing. The proof includes explicit complementary minors, a Young diagram
boundary bijection, and its permutation sign. `Partition.boundaryEquiv` and
`sign_boundary_relative_tail` record the shape interface without redefining
conjugation. No tableau formula or positivity is inferred from these identities.

[Hall/Basic](../SymmetricFunctions/Hall/Basic.lean) defines the bilinear `hall`,
normalized by `hall_hPart_mPart`, with `hall_left_nondegenerate`,
`hall_right_nondegenerate`, `hall_eq_zero_of_degrees_ne`, and the degreewise
`hallHomogeneousPerfect` equivalence and `hallHomogeneous_isPerfPair` instance.
No equivalence with the full algebraic dual of the infinite ring is asserted.
`tensorHall_tmul` specifies the explicit product tensor pairing.
[Hall/FiniteCoefficient](../SymmetricFunctions/Hall/FiniteCoefficient.lean)
identifies `hall_hPart_eq_coeff` with actual finite-alphabet coefficients.
[Hall/Hopf](../SymmetricFunctions/Hall/Hopf.lean) proves `hall_mul` against the
existing coproduct. [Finite/CompleteCoefficients](../SymmetricFunctions/Finite/CompleteCoefficients.lean)
counts complete coefficients by finite nonnegative matrices with both margins;
transposition proves `hall_symm` in [Hall/Symmetry](../SymmetricFunctions/Hall/Symmetry.lean).
`hall_mul_right`, `hall_h_eq_coeff`, and `hall_h_h` supply useful consequences.
All results assume only CommRing on coefficients; no rational descent is used.
Schur orthonormality is proved in HALL-SCHUR below.

[Finite/Bialternant](../SymmetricFunctions/Finite/Bialternant.lean) proves
`bialternant_schur`: finite specialization times `staircaseAlternant` equals
`partitionAlternant` at every alphabet size at least the number of rows.
This is a multiplication identity over arbitrary rings, not division by a
Vandermonde. [Schur/AlternantPairing](../SymmetricFunctions/Schur/AlternantPairing.lean)
exports `hall_schur_eq_alternating_coeff`, extracting the coefficient at
`Partition.shiftedRows`; negative integer determinant indices correspond to
impossible monomial divisibility. Strictly decreasing shifted rows prove the
Kronecker coefficient `coeff_partitionAlternant`.
[Hall/Schur](../SymmetricFunctions/Hall/Schur.lean) exports `hall_schur_schur`,
`hall_schur`, `hall_schur_right`, `hall_schur_homogeneous` and
`hallHomogeneous_schurBasis`. These prove the Schur normalization for the same
classical h/m Hall form, integrally including torsion and zero rings.
No tableau enumeration or positivity has been claimed.
