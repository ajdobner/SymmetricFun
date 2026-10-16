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
and convention examples. COMPLETION remains a separate unfinished milestone.


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
