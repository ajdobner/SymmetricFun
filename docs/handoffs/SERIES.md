# Bounded symmetric multivariate series

- Task SERIES; owner Codex (single worker); status done.
- Base 145fc05; MONOMIAL 73abd53, STABLE, GRADE prerequisites complete.
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 unchanged.
- Scope Realization/SeriesBasic, Realization/PowerSeries, Examples/Series.

## Proposed mathematical interfaces, before proof search

For `[CommRing R]`, define `IsSymmetricSeries f` for `f : MvPowerSeries ℕ R`
by `∀ e : Equiv.Perm ℕ, MvPowerSeries.rename e f = f`. Define its subalgebra.
Prove equivalence with coefficients depending only on the multiset of nonzero
exponents, using the existing orbit classification (including zeros).

Define `HasBoundedTotalDegree f := ∃ D : ℕ, ∀ a, coeff a f ≠ 0 →
a.sum (fun _ n => n) ≤ D`. The bounded symmetric carrier is a subalgebra
subtype: both symmetry and the one uniform bound are proofs, with no selected
bound stored as mathematical data. The intended equivalence is
`boundedSeriesEquiv R : SymmetricFunction R ≃ₐ[R] BoundedSymmetricSeries R`.
The underlying coefficient of a monomial symmetric function is exactly the
indicator of its partition shape. Finite restriction along `Fin N ↪ ℕ` is
Mathlib `killCompl` and equals the polynomial coercion of `rho R N` at every N.
Prove compatibility with elementary and complete finite polynomials and with m.

## Statement review and strategy

The implementing worker reviewed that total degree here is the sum of actual
alphabet exponents. It corresponds to weighted degree in the bounded public
ring (e_n has degree n), not ordinary degree in elementary generators. The
quantifiers are ∃D ∀a, not a separate bound for each coefficient or alphabet.
No Nontrivial, domain, rational, characteristic, or torsion assumption is allowed.
The existing polynomial-backed type remains unchanged.

Use the monomial basis to build the series map and its coefficient formula;
finite restrictions detect all coefficients and prove multiplicativity. For
surjectivity, a bounded symmetric series has finitely many partition shapes
in bounded degrees, even though its set of alphabet monomials may be infinite.
Homogeneous coordinates should also support the subsequent unrestricted
product of homogeneous components, without confusing that completion with
the bounded type or the unrestricted inverse limit of finite polynomial rings.

## Reuse and attribution

Pinned Mathlib Rename supplies actual algebra maps, coeff_embDomain_rename,
coeff_killCompl and renameEquiv. Substitution explicitly requires nilpotent
constant terms plus coefficientwise finite support of the variable family.
Consulted the inherited SymmetricPoly/MvPowerSeries Homogeneous, Symmetric,
HomogeneousSymmetric and Bases designs at source commit 98938de95a12b3ed363653cb980588e2a9188cb8.
The coefficient-shape approach and proof-irrelevant bounded subtype are credited
as design ideas. Do not copy its incomplete proofs or custom partition types;
licensing for colleague-authored proof text remains unresolved. New proofs use
pinned Mathlib and the accepted local orbit/basis APIs. Reference checkouts stay
unchanged. No accepted draft imports or proof holes are permitted.

## Validation

Pending implementation, separate statement review, full integration/axiom checks,
checker tests, declaration index and coherent commit. No SERIES result claimed yet.


## Completed implementation and independent statement review

The implementing worker reviewed the elaborated definitions and theorem types
in scripts/ReviewSeries.lean independently of the proofs. IsSymmetric is
invariance under every permutation of the actual natural-number alphabet.
HasBoundedTotalDegree has exactly one existential D before all exponent vectors;
Finsupp.degree is the sum of alphabet exponents. The carrier stores only the
series, with symmetry and boundedness as proofs. Its R-algebra equivalence is
proved in both directions and imposes only CommRing R. A series can have
infinitely many alphabet monomials despite this uniform degree bound.

seriesLinear sends the accepted m-basis to the actual coefficient-one orbit
series. Every finiteRestriction agrees with polynomial specialization rho;
these restrictions detect all coefficients, proving the algebra laws and
injectivity. coeff_toSeries identifies coefficients with full monomial-basis
coordinates. Surjectivity reconstructs from the finite set of partitions of
sizes at most D, using coefficient-orbit invariance. No desired equivalence
or basis property is assumed. isHomogeneous_toSeries and
 toSeries_homogeneousComponent identify weighted SF degree with actual alphabet
degree. finiteRestriction_toSeries_e and _h identify the elementary and complete
images at every finite alphabet; coeff_toSeries_mPart is the actual orbit formula.

Exports in SymmetricFunctions.Series: IsSymmetric, symmetricSubalgebra,
IsSymmetric.coeff_eq, isSymmetric_of_coeff_eq, monomialSeries,
HasBoundedTotalDegree and closure, boundedSymmetricSubalgebra,
SymmetricSeries, BoundedSymmetricSeries, finiteRestriction and its coefficient
formula, exists_fin_exponent, eq_of_finiteRestriction_eq, exponentPartition
and the representative/shape/degree API. SymmetricFunction exports seriesLinear,
finiteSeries, toSeries, injectivity, coefficient/symmetry/bound theorems,
boundedSeriesMap, surjectivity, boundedSeriesEquiv, inverse recovery,
homogeneous compatibility and e/h/m finite formulas.

## Validation and exact source

- python3 scripts/check_project.py: exit 0; 77 accepted modules build cleanly,
  1,448 declarations pass the transitive axiom audit, root coverage, notation
  and lambda simp regressions pass.
- python3 scripts/test_check_project.py: all five guard tests pass.
- lake env lean scripts/ReviewSeries.lean: exit 0; reviewed declarations use only
  propext, Classical.choice and Quot.sound. No holes, added axioms or native_decide.
- Lean MCP final SeriesBasic and PowerSeries diagnostics: empty.
- Examples include torsion/zero coefficient rings, the explicit uniform bound,
  a repeated exponent coefficient, empty finite alphabet, h_2 specialization,
  degree-two elementary homogeneity and inverse recovery.
- Index regenerated and git diff --check passed. Pins and reference repositories
  unchanged; no inherited draft proof text copied.

Checked source SHA-256:
SeriesBasic a717de2fe0a4e79fa79aa914b4d22a56626ba786db27ff99d1b58f2986f91904;
PowerSeries 344d33170ee537f2cc74ac22b5094d32b897149cf73a9e16622cd37593c1da04;
Examples/Series a33a4a1f2c4a5ee8a66d8fcaae248950b1f876425f5daaf87317d49de32ba15b.
The completion commit containing this handoff is the exact checked state.

Useful proof details: equivalence-to-embedding coercions need explicit change
steps for coefficient_rename rewrites; Finsupp.weight 1 needs an explicit
constant-one function before rewriting degree_eq_weight_one. Use public
LinearMap.comp_apply before reducing maps, avoiding expensive implementation
unfolding. No mathematical contract was changed. All SERIES criteria pass.
Continue immediately with COMP-ALG and the remaining COMPLETION subtasks.
