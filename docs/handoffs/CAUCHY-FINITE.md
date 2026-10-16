# Completed tensor specialization and finite Cauchy product

Owner Codex, single worker; done; base b0c9ab4. Prerequisites COMPLETION
and HALL-CORE are done. Pins unchanged. Module ownership is recorded in tasks.json.

## Precise declarations and pre-proof mathematical review

A generic degree-preserving polynomial map φ : A →ₐ[R] MvPolynomial σ R,
with φ(G_n) homogeneous of ordinary alphabet degree n, extends to
`GradedCompletion.polynomialRealization G φ hφ : GradedCompletion G →ₐ[R]
MvPowerSeries σ R`. Its coefficient at a is coeff_a(φ(component F a.degree)).
The multiplication proof uses two finite antidiagonals: exponent splits and
homogeneous-degree splits. Homogeneity kills every incompatible degree split.
This construction does not evaluate an auxiliary grading variable at 1 in an
arbitrary power series, and assumes no topology or convergence on R.

Apply it to the existing tensorDegree and tensorAlphabetSpecialization to obtain
`completedTensorSpecialization R M N : CompletedTensor R →ₐ[R]
MvPowerSeries (Fin M ⊕ Fin N) R`. Prove homogeneous component and bounded
`tensorCompletionMap` compatibility. Total degree counts both alphabets.

The finite Cauchy product is the product over i : Fin M and j : Fin N of
`MvPowerSeries.invOfUnit (1 - X(inl i)*X(inr j)) 1`. Each constant coefficient
is proved to be 1; every factor is a genuine inverse. Establish its coefficient
and homogeneous expansion as Σ_{λ : Partition d} h_λ(X)m_λ(Y), placed in
total degree 2*d, with odd components zero. A partition size-d term is degree
d in each alphabet. This is a product alphabet, distinct from Ω[X+Y].

Possible auxiliary route: finite independent-column formal series with coefficient
at Y^b equal to Π_j h_{b_j}(X), then actual joint-alphabet coefficient extraction.
Any required currying or substitution maps must be proved algebra maps, with
positive-order/substitution hypotheses discharged. No unrestricted infinite
plethysm is exposed. All coefficient assumptions remain CommRing R.

## Searches and remaining work

Pinned Mathlib has MvPowerSeries.invOfUnit/mul_invOfUnit, genuine substAlgHom
with HasSubst, homogeneous polynomial rename, and optionEquivLeft (but no general
sum-alphabet currying equivalence found in the initial search). Existing project
has tensorAlphabetSpecialization, isHomogeneous_rho, finite h/m coefficient
formulas, margin matrices, and completed finite positive substitutions.
Implementation starts with the generic coefficientwise realization and its
completed tensor instance. No acceptance criterion is yet claimed complete.

Reviewed auxiliary contract, Finite/SeriesAlphabets.lean: the sum-alphabet
currying algebra equivalence sends a joint series F to an iterated series whose
coefficient at b then a is coeff_(a.sumElim b) F. Its inverse merely reindexes
coefficients; products use the pinned Finsupp.image_sumElim_product_antidiagonal.
This is valid for arbitrary variable types, without any infinite coefficient
sums. Independent column series then have coefficient product Π_j c_j(b_j).
The iterated presentation is an auxiliary proof tool; the public tensor
specialization still targets the joint formal-series ring.

Reviewed component contract, Cauchy/Components.lean: `cauchyCompleteMonomialComponent R d`
is the finite bounded tensor Σ_{λ : Partition d} hPart λ ⊗ mPart λ,
proved to lie in tensorDegree R (2*d). Its finite coefficient at X^a Y^b
is the Cauchy product coefficient when b.degree=d and zero otherwise. The
product coefficient itself is zero unless a.degree=b.degree. These statements
then identify total homogeneous degree 2*d and prove all odd layers vanish.

## Completed checkpoint (2026-10-16)

All CAUCHY-FINITE acceptance criteria pass. Exported declarations are the proposed
polynomialRealization, completedTensorSpecialization, bounded/homogeneous
compatibility, sumSeriesEquiv, coeff_prod_subst_X, finiteCauchyProduct,
finiteCauchyProduct_mul_denominator, coeff_finiteCauchyProduct (and margin-matrix
count), cauchyCompleteMonomialComponent, its degree-2*d membership, and the
finite product's even/odd homogeneous component formulas.

Independent statement review (Codex): inspected printed definitions and all
major elaborated contracts separately from proofs. The specialization target
has actual joint finite variables; every output coefficient reads one input
component. Finite inverse factors have proved unit constant coefficient one.
The auxiliary iterated series is a proved algebra equivalence, not an
unjustified interchange of infinite sums. Coefficient and expansion statements
retain arbitrary CommRing R and include empty alphabets, torsion, zero rings,
repeated partition parts, and insufficient finite alphabets through the existing
monomial API. No completed coproduct/product-alphabet identification is assumed.

Validation, all exit 0: python3 scripts/check_project.py (126 accepted modules,
2,158 transitive axiom audits, only ordinary foundations, notation/lambda
regressions); python3 scripts/test_check_project.py (five guards);
lake env lean scripts/ReviewSchur.lean (separate statement review);
lake env lean scripts/DeclarationIndex.lean (1,549 noninternal declarations);
git diff --check. MCP Components and TensorSpecialization diagnostics clean.
Examples cover x²y²=1 and xy³=0 over ZMod 6, degree-three vanishing, empty
alphabets and bounded compatibility. Logs /tmp/cauchy-finite-{check,review}.log.
Pins and reference checkouts unchanged. Exact checked source SHA-256:
- `SymmetricFunctions/Completion/TensorSpecialization.lean`: `a23f62b98056be01078e0626d0240f8e5ef9c6648ef14d9c30f6988de10c5b39`
- `SymmetricFunctions/Cauchy/Finite.lean`: `58ac2d415f004609fa74e174383226ed515cf9e072c4e0c21da69b155bd24b7f`
- `SymmetricFunctions/Completion/PolynomialRealization.lean`: `40bb79d1b80c91998b2dd26374e7fc9c75f2e873eb4d75291c5aeac25b316e2e`
- `SymmetricFunctions/Finite/SeriesAlphabets.lean`: `3267cb52fd1d72603021a2c465de21a66734fbe8e1822fea4b5a7397c9ac4198`
- `SymmetricFunctions/Cauchy/Components.lean`: `b6e0a701f2da050d5a54d23bb562f5af41db6da20131ac81c1ab8e6d3cf91f1c`
- `SymmetricFunctions/Examples/FiniteCauchy.lean`: `0f3e3c4ae5589b7c5d80a24d97ba2498364db42a1851790a271365cb257a30ae`

Next task SCHUR-CAUCHY. Parent SCHUR is not yet complete.
