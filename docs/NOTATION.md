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
`K` are fixed. This API is still the RATIONAL milestone; the notation here
does not silently assert it or assign a lambda structure to `K`.

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
ring, `lambdaEval (-1) (p 2)` is instead `-1`. General power-sum/Adams formulas
and parameter-alphabet APIs remain PLETH/RATIONAL obligations.

Several formal alphabets in the paper mean *separate* symmetry in disjoint
sets of variables. The core Hopf maps use tensor products over the coefficient
ring and finite disjoint-union alphabets. They do not mean diagonal invariants.
Mixed objects such as `K[x₁,…,xᵣ] ⊗[K] Λ[K]` need explicit coefficient and
alphabet inclusions. The present bracket notation does not supply these APIs.

## Lowercase omega and completed uppercase Omega

Lowercase `ω` exchanges elementary and complete functions. Uppercase `Ω` is
reserved for the completed series `∑ₙ hₙ` from the paper. It has no declaration
or notation in the current bounded ring. The existing
`completeGeneratingSeries : PowerSeries (SymmetricFunction R)` has an auxiliary
series variable; it is not silently identified with the degree completion,
and evaluating that variable at `1` is not supplied.

COMPLETION must provide the completed type, its multiplication, and justified
continuity/substitution operations before `Ω` or expressions such as `Ω[A]`
are introduced. Likewise `X/(1-t)` requires a specified target and legitimate
denominators or convergence conditions. No unrestricted infinite plethysm is
asserted by this notation.

## Checks and remaining scope

[Examples/Notation.lean](../SymmetricFunctions/Examples/Notation.lean) checks
precedence, nesting, inference, aliases, and the sign convention with proofs.
[CheckNotation.lean](../scripts/CheckNotation.lean) checks import/section scope
isolation, displayed goals, and rejection of unsupported coefficient and target
types. It runs automatically in `python3 scripts/check_project.py`.

The notation pass and the basic integral plethysm laws are complete. Full PLETH
still requires Adams operations and the tensor lambda/Hopf compatibility proof.
RATIONAL and COMPLETION remain unfinished; see their exact registry contracts.
