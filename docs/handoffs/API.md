# Polynomial-backed public API

- Task ID and owner: API; Codex (single worker).
- Status: done.
- Prerequisite: ENV, checked at `f3439ea1033df550ce26723b1ff895ccad4b36a8`.
- Environment: Lean `v4.34.1`; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, unchanged.
- Implementation: `SymmetricFunctions/Basic.lean`.
- Supporting files: `SymmetricFunctions/Examples/Foundation.lean`,
  `scripts/probes/APIRepresentations.lean`, root imports, and task documentation.
- Attribution: the positive-index polynomial presentation follows
  ajdobner/SymmetricFun `SymmetricPoly/SymmFunc/Basic.lean` at upstream commit
  `98938de95a12b3ed363653cb980588e2a9188cb8`. This implementation is written against
  pinned Mathlib; no colleague proof code was copied and no draft module is imported.
  The original colleague checkout is unchanged. Redistribution licensing of the
  inherited material remains the issue recorded in `REUSE_AUDIT.md`.

## Mathematical contract

For every commutative semiring R, construct a dedicated type of finite polynomials
in elementary generators indexed by positive integers, with an R-algebra
equivalence to `MvPolynomial ℕ+ R`. For commutative rings, provide the ring
instance. The natural-indexed elementary family has `e 0 = 1`; its positive
entries freely generate the algebra. Evaluation into any commutative R-algebra
is uniquely determined by these entries. There is no nontriviality,
characteristic, torsion, grading, or stable-realization assumption.

## Representation decision

The retained, hole-free probe `scripts/probes/APIRepresentations.lean` tests both
options: a one-field wrapper with structures transported by `Equiv.commSemiring`,
`Equiv.commRing`, and `Equiv.algebra`, and a `def` type synonym with explicit
instances. Both compile algebra-map extensionality, scalar multiplication, and
`(a + b) * (a - b) = a ^ 2 - b ^ 2` by `ring`.

Choose the non-abbreviation `def` synonym. It needs fewer instance transports
and provides the required public boundary through `polynomialEquiv`. It is
semireducible, not an opaque kernel type; the policy is to use the public API
in downstream code. The accepted examples make it locally irreducible and still
prove algebra identities, generator extensionality, generation by induction,
and zero-ring and torsion-valued examples. This tests the boundary directly.

## Formal interface

The pre-proof signatures were recorded here before implementation. The final
signatures below were re-read using `#check @...`, including implicit hypotheses.
All declarations except the root type are in `SymmetricFunction`.

```lean
SymmetricFunction (R : Type*) [CommSemiring R] : Type _
polynomialEquiv (R : Type*) [CommSemiring R] :
  SymmetricFunction R ≃ₐ[R] MvPolynomial ℕ+ R
```

Under `{R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]`:

```lean
e (n : ℕ) : SymmetricFunction R
e_zero : e (R := R) 0 = 1
eval (x : ℕ+ → A) : SymmetricFunction R →ₐ[R] A
eval_e (x : ℕ+ → A) (i : ℕ+) : eval x (e (R := R) (i : ℕ)) = x i
algHom_ext {f g : SymmetricFunction R →ₐ[R] A}
  (h : ∀ i : ℕ+, f (e (i : ℕ)) = g (e (i : ℕ))) : f = g
eval_unique (f : SymmetricFunction R →ₐ[R] A) :
  eval (fun i : ℕ+ => f (e (i : ℕ))) = f
evalEquiv : (ℕ+ → A) ≃ (SymmetricFunction R →ₐ[R] A)
induction_on {P : SymmetricFunction R → Prop} (f : SymmetricFunction R)
  (C : ∀ r, P (algebraMap R (SymmetricFunction R) r))
  (add : ∀ f g, P f → P g → P (f + g))
  (mul_e : ∀ f (i : ℕ+), P f → P (f * e (i : ℕ))) : P f
```

The `e` declarations and induction use only the coefficient-ring parameters,
not A. Exported instances are `instCommSemiring`, `instCommRing`, and
`instAlgebra`; the ring instance assumes `CommRing R`.
Additional exported lemmas are `polynomialEquiv_e`, `polynomialEquiv_symm_X`,
`polynomialEquiv_e_succ`, `eval_e_zero`, `eval_e_succ`, `eval_algebraMap`,
`eval_self`, and `comp_eval`. The latter states naturality under postcomposition
by an algebra map into a further commutative R-algebra. The exact declarations
are in the source identified below.

## Statement review

The implementing worker performed a separate statement-only review of the
elaborated types after the initial pre-proof review. No contract changes were
needed. Positive elementary generators are independent; degree zero is the unit,
not another variable. Algebra-map extensionality fixes coefficients via the
R-algebra structure. Induction includes all constants and all positive generators.
The coefficient and target universes are independent. No `Nontrivial`,
characteristic-zero, or torsion-free hypothesis was introduced. The `ZMod 4`
example is an algebra evaluation, not a claimed lambda-ring instance.

## Proof strategy and useful details

Transfer polynomial structures and use `MvPolynomial.aeval` and
`MvPolynomial.induction_on`. Compare algebra maps after composition with the
inverse polynomial equivalence, using `MvPolynomial.algHom_ext`.
The ext lemma has higher priority than the polynomial lemma so downstream `ext`
uses elementary generators. Prove later maps through `eval` and `algHom_ext`.

`PNat` is a semireducible subtype in this pin. Destructing the positive index
before simplifying the two polynomial-generator lemmas avoids an unreduced
`MvPolynomial.X ⟨↑i, ...⟩ = MvPolynomial.X i` goal. In the induction constant case,
use `AlgEquiv.commutes` explicitly; unrestricted `simp` rewrites the polynomial
algebra map to `MvPolynomial.C` too early.

## Validation and integration

- `lake env lean scripts/probes/APIRepresentations.lean`: exit 0 for both choices.
- Lean MCP declaration searches, diagnostics, and goal inspection worked.
  `Basic.lean` and the foundation examples have no errors or warnings.
- MCP `lean_verify` on `SymmetricFunction.evalEquiv`: only `propext`,
  `Classical.choice`, `Quot.sound`; no suspicious source patterns.
- `python3 scripts/check_project.py`: final run exited 0, built all five
  accepted modules without warnings, and audited the transitive axioms of all
  99 accepted declarations. Only the three allowed Lean foundations occur.
- `python3 scripts/test_check_project.py`: all five checker tests passed.
- `git diff --check`: passed.
- Convention examples include `e 0`, positive generator evaluation, scalar
  multiplication and subtraction, subalgebra generation by induction, `PUnit`
  coefficients, and integral evaluation into `ZMod 4`.
- Root import coverage includes Basic, Partition, Environment, and the foundation
  examples. All accepted declarations are audited by originating module.

## Checked source state and completion

SHA-256 source identifiers (before the final commit, independent of its hash):

| File | SHA-256 |
| --- | --- |
| `SymmetricFunctions/Basic.lean` | `1d0c731e5e7bbd91abb0c4667bc010fb5abd1fd2e94e1eca4b2e0089ecd637c0` |
| `SymmetricFunctions/Examples/Foundation.lean` | `5e6b9a6c5f0585b4c9d873e6fcc66b28d2cd3a6d781d71af87540556b9fddd32` |
| `scripts/probes/APIRepresentations.lean` | `6415be51b5586cd699f87a963a4c0b1f536fd3c4dd5436a6c6ff9ff2910db635` |

All API acceptance criteria, statement review, and integration checks passed
for the exact source hashes above. GRADE, BASE, and SPEC are ready next.
Stable realization, weighted grading, Hopf structure, and the integral universal
special lambda-ring theorem remain separate obligations.

## BASE integration amendment

BASE adds the coefficient `Module` instance derived from `Algebra.toModule`
at priority 1100, resolving tensor inference with the generic integer module.
No operations or theorem statements change. See `BASE.md` for the diagnostic
and validation. Updated Basic SHA-256:
`7f2599466c19b9ebf4b81ea4a27024155ef4de0864fda8e2fc9e52a7aaacf49e`.
The full eight-module build and 194-declaration axiom audit passed.
