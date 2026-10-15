# Rational power-sum presentation and alphabet evaluation

- Task RATIONAL; owner Codex (single worker); status done.
- Prerequisites PLETH 33d7be0, HBASIS and BASE complete; MONOMIAL 73abd53 also available.
- Lean v4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 unchanged.
- Scope Plethysm/Rational, Basis/PowerSum, Alphabets, Examples/Rational.

## Contract and proposed interfaces, reviewed before proof search

For each `[CommRing R] [Algebra Q R]`, construct
`powerSumPolynomialEquiv R : MvPolynomial PNat R ≃ₐ[R] SymmetricFunction R`
with `powerSumPolynomialEquiv R (X k) = p k` for every positive k. Prove both
inverse laws. This is an ALGEBRA equivalence only. It does not identify the
canonical symmetric-function lambda operations with a polynomial lambda
structure assigning line operations to elementary generators.

Define `pPart mu` as the product of p indexed by the positive partition parts,
and transfer the partition bases along the proved degree-preserving change
of generators. Both homogeneous and whole-ring power-sum bases are intended.
No Nontrivial R assumption is necessary; a Q-algebra may be the zero ring.

For any `[CommRing A] [Algebra R A]` and specified `x : PNat -> A`, construct
`powerSumEval x : SF R ->ₐ[R] A`, with exact p-image formulas, uniqueness,
and coefficient fixation. This is coefficient-linear evaluation. It requires
no lambda structure on A and must never be described as a universal lambda
morphism into arbitrary targets.

Alphabet operations are specified by their power-sum images: virtual negation
sends p_k to -p_k; formal scaling by t sends p_k to t^k p_k. Parameter t in the
INNER alphabet is raised to its kth power. Outer coefficients in R remain
fixed by every R-algebra evaluator. Include a concrete comparison of an outer
parameter coefficient with the same parameter used inside an alphabet; even
indices must distinguish virtual minus from specializing a formal parameter
to -1.

Separately symmetric objects are tensor products of independent SF R factors,
with explicit left/right inclusions and joint evaluation maps. Mixed objects
are MvPolynomial sigma R tensor[R] SF R (finite sigma permitted) with explicit
polynomial-variable and symmetric-factor evaluations. Prove the relevant
polynomial presentations and generator/evaluation formulas. These are not
rings of invariants under a diagonal permutation action.

For X/(1-t), require the positive-index denominators `1 - t^k` to be units in
the target, for ALL k whose evaluation is defined. A convenient general API
may take units u_k with u_k.val=1-t^k, or `IsUnit (1-t^k)` for every positive k.
Then prescribe the image p_k[X] * u_k^{-1}; prove the denominator equation and
choice independence. This describes an ordinary finite-polynomial evaluation,
not the convergence of an infinite series or an unproved completion. No Ω is
introduced; uppercase Ω remains reserved for the separate completion milestone.

## Reuse search and proof plan

Read the paper's symmetric-function and plethysm conventions (lines around
600--734) read-only. Pinned Mathlib has finite Newton identities, psumPart,
polynomial evaluation, bases, and polynomial/tensor algebra equivalences;
no matching stable power-sum presentation was found by declaration search.
Reuse the local integral p_rec, whose internal indices are strictly smaller
and positive, and divide its leading coefficient only after assuming Algebra Q R.
Construct inverse elementary polynomials recursively in power-sum variables.
Prove both substitutions inverse, then package the algebra equivalence.

The public arbitrary-ring Hopf and torsion-target lambda results remain intact.
The implementer reviewed that all new rational assumptions are explicit and
that the unit-denominator condition is stronger than merely 1-t being a unit,
which would not suffice for all positive k. No accepted contract is changed.

## Completed interface

The inverse Newton recurrence `elementaryPowerCoordinates` uses formal e_i as
coordinate variables, with `inverseNewtonCoefficient` the mapped reciprocal of
the signed positive integer. `powerSumSubstitution` sends e_i to p_i;
`inversePowerSumSubstitution` is its proved inverse in both directions.
`powerSumChangeOfGenerators` packages that change as an algebra equivalence;
`powerSumPolynomialEquiv` presents SF R by independent power-sum variables.
Both substitutions preserve weighted degree; `powerSumHomogeneous` restricts
the equivalence to any degree.

`pPart` is the product of positive power sums with partition multiplicities;
`pPart_eq_prod_positiveParts` identifies it with the literal product over parts.
`pBasis` and `pBasisAll` are the homogeneous/full partition bases, with apply
and inverse-polynomial coefficient formulas. `powerSumEval` and
`powerSumEvalEquiv` give arbitrary p-image evaluation and uniqueness;
`powerSumEval_p`, `_e_one`, `_algebraMap`, `algHom_ext_p`, and
`comp_powerSumEval` keep its public use independent of the implementation.

`negativeAlphabetEval`, `scaledAlphabetEval`, `sumAlphabetEval`, and
`productAlphabetEval` give their exact p-image formulas. `powerSumAdams` fixes
R-coefficients and multiplies positive indices. It has identity/composition
laws; `alphabetSpecialization_powerSumAdams` proves it raises actual finite
alphabet variables to powers. `powerSumEval_psum` recovers finite specialization.

`tensorPowerSumPolynomialEquiv` presents the two independent symmetric factors;
`tensorAlphabetEval` has pure-tensor, generator, and uniqueness formulas.
Its composition with comultiplication is the sum-alphabet evaluator.
`MixedAlphabet` is MvPolynomial sigma R tensor[R] SF R;
`mixedPowerSumPolynomialEquiv` presents its independent generator blocks.
`mixedAlphabetEval` has parameter/symmetric evaluation and uniqueness laws.
`mixedAdams` acts on inner ordinary variables and power-sum indices, with
identity/composition laws; `mixedPlethysticEval` prescribes these p-images.

`geometricAlphabetEval t h x` uses h : forall positive k, IsUnit (1-t^k).
Its p-image, denominator equation, and uniqueness are proved without a field
or domain hypothesis. `geometricAlphabetEval_p_field` is the familiar quotient
formula when the target is a field. The examples prove all needed units in
RatFunc Q using injectivity of the polynomial embedding and the nonzero
constant coefficient of 1-X^k. They do not assume the denominators are units
in the ordinary polynomial ring.

## Separate mathematical statement review

After compilation, the implementing worker ran `scripts/ReviewRational.lean`
and reviewed its printed definitions and fully elaborated types independently
of the proof bodies. The signed reciprocal occurs only under Algebra Q R;
its invertibility is proved by mapping the rational identity, so zero coefficient
rings remain allowed. Both Newton substitutions are proved inverse before any
basis or polynomial independence claim is used. Weighted degree is preserved
in both directions; the p-basis vector is the actual multiplicity product of p.

The polynomial presentation is an ALGEBRA equivalence. No lambda instance is
transported along it and no elementary generator is declared a line element.
`powerSumEval` fixes the specified R-algebra coefficient map and has arbitrary
commutative R-algebra targets. It is not asserted to preserve lambda operations.
The integral `lambdaHomEquiv` retains every special target, including torsion.
The printed monomial basis over ZMod 2 and the rational basis over PUnit check
these different coefficient assumptions remain separate.

Virtual minus negates every positive-index image. Scaling gives t^k times that
image, while an outer coefficient remains unchanged. Mixed Adams applies power
substitution to actual polynomial parameter variables and multiplies symmetric
power-sum indices; its finite-alphabet compatibility is proved. The tensor base
is explicitly R, and the two generator blocks are independent. No diagonal
permutation invariance or unspecified generic tensor lambda structure is used.
The geometric evaluator requires units at every positive k, including even k;
the denominator characterization proves independence of choices. No completed
type, convergence assertion, or uppercase Omega is introduced.

## Validation and exact checked state

Checked source state: the RATIONAL completion commit containing this handoff.
- `python3 scripts/check_project.py`: exit 0; all 74 accepted modules build
  without warnings, root-import coverage and task DAG checks pass; all 1,367
  declarations pass the transitive axiom audit. Both notation and public lambda
  simp regression scripts pass, including the original reported plain-simp goal.
- `lake env lean scripts/ReviewRational.lean`: exit 0. Reviewed representative
  equivalences, bases, evaluation uniqueness, tensor/Hopf agreement, Adams
  composition, and rational-function denominator proofs use only propext,
  Classical.choice, and Quot.sound.
- `lake env lean scripts/DeclarationIndex.lean`: exit 0; 1,037 noninternal
  declarations indexed. Lean MCP final example diagnostics: empty. Goal display
  inspection shows Λ[R] and the explicit coefficient map in the parameter test.
- `python3 -m unittest discover -s scripts -p 'test_*.py'`: five guard tests pass.
- `git diff --check`: passed. Pinned dependency files unchanged; reference
  checkouts read only. No colleague proof text was copied for this milestone.

SHA-256 of the checked sources:
- Plethysm/Rational: `b8d5e9ae4606175e1c5aca851b7b3ace90e6587b8dcbb85f0e3ee32abc7f4a08`.
- Basis/PowerSum: `97b4af4015cc11cd2a2d90b09b9258141699bc884b2c8122b00c6d53d37c1bad`.
- Alphabets: `83587749ad5332a97908dd02b3cac75c6639aa7d839e89717706e36c1e892e7b`.
- Examples/Rational: `455bde84b0d70f1b4a69e08588a2cfa96d13f21eceaae6ae86b00c3028cbf840`.

Useful implementation details: restricted homogeneous equivalences need explicit
coercions in map_add/map_smul proofs. `p 1` simplifies to `e 1`, so public
powerSumEval_e_one and powerSumAdams_e_one supply that normal form. Tensor
notation around powers needs parentheses. Unit-dependent denominators are
rewritten by simplifying the unit-cancellation theorem, avoiding an invalid
dependent rewrite motive. All final proofs are local kernel-checked proofs.

All RATIONAL acceptance criteria pass. Together with LSIMP 9aa493d, PLETH
33d7be0, and MONOMIAL 73abd53, this completes the user's current repair and
three-extension goal. No obligations remain within that goal. SERIES and SCHUR
are ready by prerequisites; SCHUR first requires its specified task breakdown
and statement review. COMPLETION waits for SERIES. External publication,
proving-service uploads, and those further extensions remain outside this run.
