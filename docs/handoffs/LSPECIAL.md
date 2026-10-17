# Special identities for signed polynomial lambda operations

- Task: LSPECIAL; owner: Codex (single worker); status: done.
- Prerequisite: LLINE 329c16f; LPOLY f49cd2f supplies fixed universal polynomials.
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- Scope: LambdaRing/Polynomial/{Positive,Newton,Rational,Density,Special}.lean.
- No colleague code copied; dependencies remain pinned.

## Mathematical contract

For every variable type sigma and all integer polynomials f,g, prove
operation_n(f*g)=P_n(operation_i(f), operation_j(g)), and
operation_n(operation_m(f))=Q_(n,m)(operation_i(f)). All n,m are natural,
including zero, and coefficients may be negative. Package SpecialLambdaRing
for the existing LLINE PreLambdaRing instance. The already-proved preserving
monomial substitutions then apply between actual special lambda rings.
No result for arbitrary torsion targets is inferred by rationalization here.

## Reviewed decomposition before proof search

Chosen route: explicit polynomial identities in the signed coefficients,
using a rational Newton recurrence as an auxiliary polynomial expression.
This is not an assumed Adams criterion.

1. Positive case: for any finite family x of zero or coefficient-one monomials,
   prove operation_n(sum x)=elementaryValue x n. Products and squarefree
   products of such monomials remain line monomials. Apply LPOLY's product and
   iteration evaluation identities to obtain both special laws on positive
   sums. Every natural-coefficient polynomial is such a finite sum, with
   multiplicities included in its finite index type.
2. Integral Newton recurrence: define psi_k by X_i -> X_i^k with coefficients
   fixed. Compute the logarithmic derivative of the *constructed* totalUnit
   using derivative(u)*u^-1, its product rule, and signed powers. Its coefficient
   n is (-1)^n psi_(n+1)(f). Thus prove the undivided Newton recurrence for
   operation_n(f), including signed coefficients, directly from the unit product.
3. Auxiliary rational operation: over MvPolynomial sigma R for any commutative
   Q-algebra R, recursively define the coefficients by the divided Newton
   recurrence. Prove naturality in coefficient algebra maps and prove that
   mapping the LLINE integer operations into Q gives this recurrence's unique
   solution. This step must be proved, never assumed from Adams terminology.
4. Polynomial density: replace each coefficient of f (and separately g) on its
   finite support by an independent indeterminate over Q. The recursive operations
   and both sides of each special identity are actual polynomials in those
   parameters. Specialization at every nonnegative integer parameter tuple
   satisfies the identity by steps 1-3. Use pinned MvPolynomial.funext_set over
   the infinite natural-number subset of Q, coefficientwise in alphabet variables,
   to prove the parameter polynomial identity. Specialize arbitrary rational
   coefficients, then apply injectivity of Z-polynomial -> Q-polynomial to
   deduce both identities for every signed integer polynomial.
5. Instantiate SpecialLambdaRing only after both identities are proved; check
   negative examples and zero indices; separately review all elaborated statements,
   full project build, transitive axiom audit, and checkpoint documentation.

## Independent mathematical review of the strategy

Each stage preserves the fixed P_n and Q_(n,m) from LPOLY. Parameter evaluation
acts on coefficients; psi_k fixes those parameters, so it commutes with that
evaluation. Natural parameter values give finite sums of monomial line elements.
Density is legitimate because each expression is a finite polynomial in finitely
many occurring parameters even if the ambient index type is infinite. The
nonnegative integers form an infinite subset of Q. Final descent is only along
the injective coefficient map Z -> Q in polynomial rings, not into a torsion
lambda target. All missing lemmas above are proof obligations, not added axioms.
This route supports later torsion-target freeness via the integral special laws.

## Current status

No LSPECIAL identity is accepted at this initial handoff. Next: finite positive
line alphabets and their two special identities. The main unresolved step is
polynomial-density extension through the rational Newton recurrence.

## Implemented proof chain and exports

- Positive: `totalUnit_sum`, `operation_sum_lines`, product/iteration identities
  on finite line alphabets, `MultiplicityAlphabet` and its sum formula, and
  `operation_mul_natSum` / `operation_iterate_natSum`. The multiplicity alphabet
  includes each occurrence, so natural coefficients are not mistaken for lines.
- Newton: `logDerivative`, its additive hom on units and signed-power law,
  `coeff_logDerivative_lineUnit`, `coeff_logDerivative_totalUnit`, and the
  undivided `operation_newton` for arbitrary signed integer polynomials.
- Rational: `rationalOperation` is well-founded recursion with attached finite
  antidiagonals; `rationalOperation_succ`, coefficient algebra-map naturality,
  and `map_operation_eq_rationalOperation` for every commutative Q-algebra.
- Density: integral aeval naturality with explicit algebra instances;
  `eq_of_eval_nat`, `eq_of_map_eval_nat`, `parameterPolynomial` and specialization;
  positive rational identities, parameter identities, and finally
  `rationalOperation_mul` / `rationalOperation_iterate` for all rational polynomials.
- Special: `operation_mul`, `operation_iterate`, the actual SpecialLambdaRing
  instance on MvPolynomial sigma Z, and preserving `renameHom` / `setZeroHom`.
  General preserving monomial substitutions from LLINE now connect special rings.

## Separate final statement review

The same worker reviewed `.scratch/LSpecialReview.lean` separately from proof
acceptance. Both final integral identities quantify over every polynomial,
without coefficient-sign, characteristic, or degree hypotheses, and every
natural n,m. They use exactly LPOLY's fixed integral P_n and Q_(n,m).
The negative case is not assumed: it follows through a proved Newton comparison,
polynomial identities tested at all natural parameter tuples, and the injective
integer-to-rational polynomial coefficient map. The final instance refers to
LLINE's existing operations. It is not an instance on a new rationalized type.
The auxiliary rational hypotheses occur only in the auxiliary statements.
No criterion about Adams operations over torsion rings was assumed or used.
Accepted examples exercise lambda_2(-X_i)=X_i^2 and lambda_2(lambda_0(f))=0.

## Validation and completion

Exact checked state: the commit containing this completion handoff.
- `python3 scripts/check_project.py`: exit 0; all 49 accepted modules built,
  root coverage checked; 929 declarations passed transitive axiom inspection.
- `python3 scripts/test_check_project.py`: exit 0; five tests passed.
- `lake env lean .scratch/LSpecialReview.lean`: exit 0; separate type review,
  instance synthesis, direct product/iteration axiom audits. Only propext,
  Classical.choice and Quot.sound occur.
- Lean MCP final diagnostics for Positive, Newton, Rational, Density, Special:
  empty; `git diff --check` passed.
- Pins and original colleague checkouts unchanged; no new proof assumptions.

All LSPECIAL acceptance criteria pass. LSTABLE is ready. The stable integral
special lambda structure, free-object theorem for arbitrary torsion targets,
and RELEASE validation remain unfinished.

Useful engineering notes: generic integral aeval naturality must quantify over
explicit Algebra Z instances; specializing a helper fixed to the canonical
integer algebra can fail to rewrite polynomial-algebra instances. Explicitly
type attached-sum lambdas to avoid expensive recursive-definition unification.
