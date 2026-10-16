# Notation, alphabets, and coefficients

The conventions follow the symmetric-functions and plethystic-evaluation sections
of *Flagged LLT polynomials, nonsymmetric plethysm, and nonsymmetric Macdonald
polynomials*, especially `e:Omega`, `ss:plethysm` (i)–(iv), and `ss:coefficients`.
The local source was read without modification at
`/home/ghseeli/flagged-llt-polynomials/Flagged plethysm and LLTs.tex`.

## Activation and declaration names

```lean
import SymmetricFunctions.Notation

open SymmetricFunction
open scoped SymmetricFunctionNotation

example (f g k : Λ[ℤ]) : (f⟦g⟧)⟦k⟧ = f⟦g⟦k⟧⟧ :=
  plethysm_assoc f g k

example {R : Type*} [CommRing R] (f : Λ[R]) : ω (ω f) = f :=
  omega_omega f

example (n : ℕ) (f : Λ[ℤ]) : (elementary n)⟦f⟧ = λ[n] f :=
  plethysm_e n f
```

Importing this module, or the root `SymmetricFunctions`, does not activate the
notation. `open SymmetricFunction` makes declaration names available; the separate
`open scoped SymmetricFunctionNotation` enables syntax. Both commands can be
limited to a `section`, or use `open scoped SymmetricFunctionNotation in` for
one declaration. Unrelated Mathlib scopes also use omega and double brackets;
use the descriptive declarations if simultaneously opened scopes conflict.

| Notation | Underlying declaration | Scope of the operation |
| --- | --- | --- |
| `Λ[R]` | `SymmetricFunction R` | Bounded, polynomial-backed symmetric functions. The type supports `CommSemiring R`; the ring and Hopf results use `CommRing R`. |
| `Ω` | `SymmetricFunction.completeSeries` | Degree-completed symmetric functions, with component n equal to h_n; coefficient ring inferred from context. |
| `ω f` | `SymmetricFunction.omega f` | The elementary-complete involution over any commutative coefficient ring. `ω` itself is an algebra equivalence. |
| `λ[n] a` | `LambdaRing.lambda n a` | Exterior powers on any `CommRing A` with a specified `PreLambdaRing A`; natural index, including zero. |
| `f⟦g⟧` | `SymmetricFunction.plethysm f g` | Both arguments are in `Λ[ℤ]`, outer argument first; definitionally `lambdaEval g f`. |

[Names.lean](../SymmetricFunctions/Names.lean) also supplies searchable aliases
`elementary`, `complete`, `powerSum`, and `elementaryCompleteInvolution` for
`e`, `h`, `p`, and `omega`. These are definitionally equal: existing callers,
lemma names, and simplification proofs continue to work. Standard short names
were retained rather than deprecated. Elementary and complete indices are
natural, with `e 0 = h 0 = 1`; power-sum indices are positive (`ℕ+`).

The existing `lambdaEvaluation a` is the underlying ring map, whereas
`lambdaEval a` is the map packaged with proof that it preserves exterior powers.
Both take the chosen target element first. The new `plethysm f g` puts the
outer function first, matching the paper's order. The existing
`SymmetricFunction.eval` specifies **elementary** generator images; it is not
an evaluator specified by power-sum images.

Public simplification keeps `LambdaRing.lambda n a`. The bridges
`SymmetricFunction.lambda_eq_lambdaOperation` and
`LambdaRing.Polynomial.lambda_eq_operation` are available for explicit rewriting,
but do not run automatically in `simp`. Generator, zero, unit, and signed-input
identities therefore simplify at the public API. The polynomial presentation is
an algebra equivalence only: its line-element polynomial lambda structure differs
from the canonical stable lambda structure on symmetric functions.

## Precedence and displayed goals

Brackets bind tightly and delimit the full inner expression. Chaining is left
associated; explicit nested brackets give the other association. Ordinary Lean
function application and the exterior-power prefix bind more tightly than sums,
products, and powers. A bracketed application can itself be their argument.

| Input | Parses as |
| --- | --- |
| `f + g⟦k⟧` | `f + (g⟦k⟧)` |
| `(f + g)⟦k⟧` | Plethysm with the sum as outer argument |
| `f⟦g⟧^2` | `(f⟦g⟧)^2` |
| `f⟦g⟧⟦k⟧` | `(f⟦g⟧)⟦k⟧` |
| `f⟦g⟦k⟧⟧` | Plethysm of `f` with `g⟦k⟧` |
| `ω f⟦g⟧` | `ω (f⟦g⟧)` |
| `(ω f)⟦g⟧` | Plethysm with `ω f` as outer argument |
| `λ[n] f⟦g⟧` | `λ[n] (f⟦g⟧)` |
| `λ[n] f^2` | `(λ[n] f)^2` |
| `λ[n] λ[m] f` | `λ[n] (λ[m] f)` |

Parenthesize mixed unary and bracketed expressions when intent may be unclear.
Also parenthesize a function application used as the outer term, as in
`(elementary n)⟦g⟧`.
The tests check these parses by definitional equality, not by identities that
could conceal a precedence error. Associativity is proved separately.

The regression script checks that Lean displays goals such as

```text
f g k : Λ[ℤ]
⊢ f⟦g⟧⟦k⟧ = f⟦g⟦k⟧⟧

f : Λ[ℤ]
⊢ ω (ω f) = f
```

Use `set_option pp.notation false in` when inspecting the underlying names.

## Alphabet and coefficient roles

The paper's alphabet `X` in a plethystic argument denotes the sum of its letters.
In the integral free lambda ring, its representative is `e 1`: both
`(e 1)⟦g⟧ = g` and `f⟦e 1⟧ = f` are proved. This does not identify every
symmetric function with a list of letters. No extra alphabet syntax is introduced.

Integral plethysm uses the actual constructed special lambda structure. It is
a ring and lambda morphism in the outer argument; it is not generally additive
in the inner argument. For an arbitrary special target `A`, including targets
with torsion, use `lambdaEval a f`. The bracket notation deliberately has the
more specific type `Λ[ℤ] → Λ[ℤ] → Λ[ℤ]`.

The paper also uses coefficient-linear power-sum evaluation: for a commutative
`ℚ`-algebra `K`, a commutative `K`-algebra `A`, and specified images of every
positive power sum, there is a `K`-algebra evaluation. Outer coefficients in
`K` are fixed. Use `SymmetricFunction.powerSumEval x f`, where `x : ℕ+ → A`.
The proved `powerSumPolynomialEquiv K` sends the formal variable `X k` to `p k`;
`powerSumEvalEquiv` expresses the unique coefficient-algebra evaluation property.
It assigns no lambda structure to `K` or `A`. The integral double brackets
remain integral; they are not overloaded for coefficient-linear evaluation.

A parameter's role matters. When `t` occurs inside a formal alphabet, it is an
indeterminate letter and power substitution sends it to `t^k`. When `t` is
an outer coefficient of `f` in a coefficient-linear evaluation, it is fixed.
For example, the paper's conventions give

\[
p_k[tX]=t^k p_k[X],\qquad p_k[-X]=-p_k[X],\qquad
(t p_k)[X]=t p_k[X].
\]

Here `-X` is virtual additive negation. Replacing every letter `x_i` by `-x_i`
instead gives `(-1)^k p_k[X]`. Thus computing with an indeterminate `t` and
then specializing `t=-1` does not give virtual negation in even degrees.
The notation does not treat an arbitrary scalar as a line element or make its
ordinary ring specialization into a lambda morphism.

The accepted convention examples demonstrate this distinction in degree two:
`lambdaEval (MvPolynomial.X ()) (p 2)` is the square of the variable; setting
that variable to `-1` gives `1`. In the same proved polynomial special lambda
ring, `lambdaEval (-1) (p 2)` is instead `-1`. The integral `plethysm_p` and `plethysm_p_neg` prove the general Adams and
virtual-negative formulas. For rational coefficient-linear evaluation use
`negativeAlphabetEval x` and `scaledAlphabetEval t x`; their p-image formulas
hold for every positive index.

Several formal alphabets in the paper mean *separate* symmetry in disjoint
sets of variables. The core Hopf maps use tensor products over the coefficient
ring and finite disjoint-union alphabets. They do not mean diagonal invariants.
`tensorAlphabetEval x y` assigns independent p-images to the two factors of
`Λ[K] ⊗[K] Λ[K]`. Its composition with the coproduct is `sumAlphabetEval x y`.
`MixedAlphabet σ K` is explicitly `MvPolynomial σ K ⊗[K] Λ[K]`;
`mixedAlphabetEval z x` assigns the ordinary variables and symmetric p-images.
The polynomial presentations use the disjoint variable sets `ℕ+ ⊕ ℕ+` and
`σ ⊕ ℕ+`, respectively.

For an inner mixed expression `g`, `mixedPlethysticEval g f` evaluates the outer
function f with p_k image `mixedAdams k g`. This raises the ordinary variables
inside g to kth powers and replaces p_n by p_(kn), fixing K throughout. Thus
an inner parameter is stored in the polynomial tensor factor. An outer parameter
belonging to K is fixed by the K-algebra map. The APIs use descriptive names to
keep these roles visible; no extra alphabet syntax is required.

## Lowercase omega and completed uppercase Omega

Lowercase `ω` exchanges elementary and complete functions in the bounded ring.
Uppercase `Ω` denotes `completeSeries : DegreeCompletion R`, with degree-n
component `h n`. It is available in the same opt-in scope and has no bounded
interpretation. `signedElementarySeries` has component `(-1)^n • e n` and is
its two-sided inverse; `completeSeriesUnit` packages this inverse explicitly.
`elementarySeries` and `signedCompleteSeries` satisfy the other signed identity.

```lean
open SymmetricFunction
open scoped SymmetricFunctionNotation
example : DegreeCompletion.component ℤ Ω 2 = h 2 := by simp
example : (Ω : DegreeCompletion ℤ) * signedElementarySeries = 1 := by simp
example : completedFiniteSpecialization ℤ 0 Ω = 1 := by simp
```

`completedFiniteSpecialization R N Ω` is a justified restriction of the actual
alphabet to Fin N. Its degree-n projection is the series inclusion of the finite
complete polynomial h_n. The old `completeGeneratingSeries` has an auxiliary
bookkeeping variable; no operation substitutes 1 into an arbitrary formal series.
General completed substitutions require separate proved finiteness hypotheses;
Ω cannot be passed to the bounded integral `f⟦g⟧` operation.

For bounded symmetric functions, `geometricAlphabetEval t h x`
implements `X/(1-t)` when `h : ∀ k : ℕ+, IsUnit (1-t^k)` in the target. Its
kth p-image is x_k times the inverse unit; in a field this is x_k/(1-t^k).
The denominator equations uniquely determine the map. The condition is on
**every** positive k, not merely k=1. The ℚ(t) example proves all these units.
Only a finite polynomial in p is evaluated; no unrestricted infinite plethysm
or convergence assertion follows.

## Checks and remaining scope

[Examples/Notation.lean](../SymmetricFunctions/Examples/Notation.lean) checks
precedence, nesting, inference, aliases, and the sign convention with proofs.
[CheckNotation.lean](../scripts/CheckNotation.lean) checks import/section scope
isolation, displayed goals, and rejection of unsupported coefficient and target
types. It runs automatically in `python3 scripts/check_project.py`.

The notation pass, full integral plethysm, and tensor lambda/Hopf compatibility
are complete. Rational evaluation and mixed alphabets have their own named API
and convention examples. SERIES and COMPLETION are complete with the certified
operations documented below; SCHUR remains subsequent work.


## Bounded symmetric-series realization

`SymmetricFunction.boundedSeriesEquiv R` identifies Λ[R] with
`SymmetricFunctions.Series.BoundedSymmetricSeries R`. Its bound is the proposition
`∃ D, ∀ a, coeff a F ≠ 0 → a.degree ≤ D`, not a selected bound or finite support
in the infinitely many alphabet variables. `toSeries R` is the underlying
algebra map; `finiteRestriction R N` sets variables outside Fin N to zero and
recovers `rho R N`. Weighted homogeneous projections agree in both realizations.
The degree completion now supplies Ω, with its certified finite restrictions.

## Degree-completion names

`SymmetricFunction.DegreeCompletion R` is the product of weighted homogeneous
pieces. `DegreeCompletion.component R F n` returns a bounded homogeneous function;
`DegreeCompletion.truncate R D F` sums degrees zero through D. Qualify `truncate`
when both bounded and completed APIs are in scope. `completionEmbedding R` is the
injective algebra map from `Λ[R]`. No new notation is needed for these operations.
Ω uses this completed type; its component and inverse identities are proved.

`completionSeriesEquiv R` identifies the degree completion with all symmetric
`MvPowerSeries ℕ R`. `completedFiniteSpecialization R N` restricts an alphabet to
`Fin N`, with a formal power-series result. On `completionEmbedding R f` it is
exactly the series inclusion of `rho R N f`. These operations use actual alphabet
variables and total alphabet degree, matching weighted symmetric-function degree.

For completed alphabet addition, `completedCoproduct R Ω` equals
`completedTensorProduct R Ω Ω`. The latter is an external product in
`CompletedTensor R`, whose nth component sums `F_i ⊗ G_j` over i+j=n.
This target is the product of total-degree tensor pieces. No ordinary tensor
product of two completions is used, and no extra custom tensor notation is needed.

## Certified completed evaluation

Import `SymmetricFunctions.Completion` for the completed operations, and
`SymmetricFunctions.Notation` plus `open scoped SymmetricFunctionNotation` for Ω.
The root import includes both modules without opening the scope.

- `completedSubstitution a ha` substitutes actual alphabet letters
  `a : ℕ → MvPowerSeries τ R`. The certificate `ha : MvPowerSeries.HasSubst a`
  requires nilpotent constant terms and a coefficientwise finite family.
- `hasSubst_of_positive_locallyFinite a h0 hfinite` supplies that certificate
  from zero constant terms and finiteness of each set of letters contributing
  a nonzero specified coefficient. Infinitely many identical nonzero letters
  fail the latter condition, even if all have positive degree.
- `completedFiniteEval a h0` uses `a : Fin N → MvPowerSeries τ R`. Here zero
  constant terms suffice because the family is finite. It first restricts the
  alphabet to Fin N, then applies Mathlib's certified substitution algebra map.

Each operation fixes outer R-coefficients. On bounded inputs,
`completedFiniteEval_embedding_eq_eval` identifies it with the existing elementary
image evaluator; `completedFiniteEval_embedding` gives the concrete polynomial
formula `MvPolynomial.aeval a (rho R N f).val`.

`completedSubstitution_coefficient_finite` proves finiteness of the terms in each
output coefficient, and `coeff_completedSubstitution` states the finite-support
sum. With zero constant terms, `truncTotal_completedSubstitution` and
`truncTotal_completedFiniteEval` prove that output degrees through D depend only
on input components through D. These polynomial-valued truncation theorems use
`Finite τ`, as required by Mathlib; evaluation itself allows arbitrary τ.

```lean
open SymmetricFunction
open scoped SymmetricFunctionNotation
example : completedFiniteEval
    (fun _ : Fin 1 => (MvPowerSeries.X (0 : Fin 1) : MvPowerSeries (Fin 1) ℤ))
    (by simp) Ω * (1 - MvPowerSeries.X 0) = 1 :=
  completedFiniteEval_complete_one_mul _ (by simp)
```

Thus one positive-degree letter evaluates Ω to the geometric inverse of `1-a`.
`hasSubst_positivePowers s` certifies the infinite alphabet `X_s, X_s², X_s³, …`:
at exponent d only indices at most d.degree can contribute. This is an actual
finiteness proof, independent of merely having units `1-t^k`.

The `completedSubstitution_apply` and `completedFiniteEval_apply` bridges are
explicit rewrites, not automatic simp rules. Public identity, bounded-input and
one-letter simp lemmas therefore remain visible. No `Ω[A]` or unrestricted
completed plethysm syntax is introduced. These coefficient-linear alphabet maps
do not conflate virtual negation with replacing each letter by its negative,
and do not manufacture an Adams action on arbitrary outer parameters.

## Partition rows and determinant indices

`SymmetricFunctions.Partition.rowLength ξ i` numbers rows from zero in decreasing
order and returns zero after `Partition.length ξ`. Its source is Mathlib's
`YoungDiagram.ofPartition ξ`, and `ξ.conjugate` is Mathlib's conjugation.
`Partition.Contained μ ξ` is Young diagram containment; the sizes may differ.
`Partition.FiniteTableau ξ N` bounds the entries of Mathlib's semistandard
tableau on shape cells by N. No tableau generating formula is asserted yet.

Lean reserves bare `λ` for anonymous functions, so declarations use `ξ` or `μ`
for partitions. Jacobi–Trudi indices will have the form
`(rowLength ξ i : ℤ) - (i : ℤ) + (j : ℤ)`: all casts precede subtraction.
No new partition syntax or replacement partition type is introduced.

`SymmetricFunction.schur ξ` is the descriptive Schur function API.
`completeInt (-1) = 0`, while `completeInt 0 = 1`; in a determinant use
`jacobiTrudiMatrix ξ L` and provide `Partition.length ξ ≤ L` to
`det_jacobiTrudiMatrix`. `finiteCompleteInt N` uses the identical convention for
finite complete polynomials. For the partition (2,1), the accepted example
computes `schur ξ = h 2 * h 1 - h 3`. The column identity uses Mathlib's
`(Nat.Partition.indiscrete n).conjugate`. No additional custom syntax is needed.

`schurBasis R d ξ` is a vector in the degree-d homogeneous submodule;
`schurBasisAll R ⟨d, ξ⟩` is its bounded-ring value. Both coerce/simplify to
`schur ξ`. Their `repr` maps give Schur coefficients. The proof-only ordering
statistic `Partition.squareWeight` is the sum of squared parts: for (2,2) it is
8, while the symmetric-function degree remains 4.

`ω (schur ξ)` simplifies to `schur ξ.conjugate`. For the dual determinant,
use `elementaryJacobiTrudiMatrix ξ.conjugate L`; `dual_jacobiTrudi` requires
`Partition.length ξ.conjugate ≤ L`. Supplying ξ itself instead gives
`ω (schur ξ)` via `det_elementaryJacobiTrudiMatrix`. As with `completeInt`,
`elementaryInt` uses integer indices, zero below zero and one at index zero.
The (2,1) example proves the shape self-conjugate and omega fixes its Schur
function over ZMod 6.

The Hall pairing is written `hall f g`; its explicit tensor counterpart is
`tensorHall z w` (open `scoped TensorProduct` for `⊗ₜ[R]`). No pairing syntax
is added. `hall_hPart_mPart ⟨d, μ⟩ ⟨e, ν⟩` uses sigma partition indices, so
its Kronecker delta includes equality of the degrees. `hallHomogeneousPerfect R d`
is the perfect pairing on degree d only. For example, over ZMod 6,
`hall (h 2 ^ 2) (mPart (2,2)) = 1`: repeated parts introduce no factorial.
Here `(2,2)` is explanatory shape notation; Lean uses Nat.Partition.ofSums.
`hall_h_eq_coeff` is a coefficient in one actual alphabet variable, not a
virtual-alphabet substitution. See Examples/Hall.lean for fully elaborated examples.

`hall (schur ξ) (schur μ)` is the classical Schur Kronecker pairing; use
`hall_schur_schur` with sized sigma indices to include unequal degrees.
`hall_schur` reads the full Schur coefficient. The finite polynomial
`staircaseAlternant N` uses decreasing exponents N-1-i, and
`partitionAlternant ξ N` adds the row lengths. `Partition.shiftedRows ξ N`
is its coefficient exponent vector. Bialternant statements are multiplication
identities, so they remain meaningful over arbitrary rings without a notation
for dividing by the staircase. Examples/HallSchur.lean checks (2,1), torsion,
zero rings, empty alphabets, extra padding, and negative-index coefficients.

`skewing f g` denotes the bounded adjoint f-perp applied to g;
`hall_skewing` states `hall (skewing f g) k = hall g (f*k)`.
`skewSchur ξ μ` is schur μ-perp applied to schur ξ. Public simplification
uses `skewing_one` and `skewing_zero`; `skewing_apply` is deliberately not a
simp lemma because it exposes the finite contraction implementation.
No new postfix syntax is required. `skewJacobiTrudiMatrix ξ μ L` uses
`(rowLength ξ i : ℤ) - (rowLength μ j : ℤ) - (i : ℤ) + (j : ℤ)`.
`skew_jacobiTrudi` identifies its determinant with `skewSchur ξ μ` whenever
L bounds both lengths, including noncontained shapes. For example, the skew
row (3)/(1) equals h 2, whereas a two-row inner shape (1,1) inside a single
row (3) gives zero despite its smaller size. These are checked examples over
arbitrary rings; extra padding is also checked over ZMod 6.
`sumAlphabetSpecialization R N` means left plus right alphabets, with the left
bounded symmetric functions as coefficients. It is an actual algebra map.
No new bracket notation or infinite plethysm is introduced.
