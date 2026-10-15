import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.PNat.Basic

/-!
# The polynomial-backed ring of symmetric functions

`SymmetricFunction R` is a dedicated type synonym for finite polynomials in
positive-indexed elementary generators. Use `polynomialEquiv`, `eval`, and
`algHom_ext` at the representation boundary; downstream proofs need not unfold
the type. This file does not yet identify it with stable symmetric polynomials.

The positive-index presentation follows the proposal in ajdobner/SymmetricFun,
`SymmetricPoly/SymmFunc/Basic.lean` (commit 98938de95a12b3ed363653cb980588e2a9188cb8).
The implementation below uses Mathlib's polynomial API directly.
-/

/-- Finite polynomials in the positive elementary symmetric functions.
The degree relevant to symmetric functions assigns weight `i` to generator `i`;
it is not the ordinary polynomial degree in these generators. -/
def SymmetricFunction (R : Type*) [CommSemiring R] := MvPolynomial ℕ+ R

namespace SymmetricFunction

noncomputable section

instance (R : Type*) [CommSemiring R] : CommSemiring (SymmetricFunction R) :=
  inferInstanceAs (CommSemiring (MvPolynomial ℕ+ R))

instance (R : Type*) [CommRing R] : CommRing (SymmetricFunction R) :=
  inferInstanceAs (CommRing (MvPolynomial ℕ+ R))

instance (R : Type*) [CommSemiring R] : Algebra R (SymmetricFunction R) :=
  inferInstanceAs (Algebra R (MvPolynomial ℕ+ R))

/-- The explicit polynomial presentation. -/
def polynomialEquiv (R : Type*) [CommSemiring R] :
    SymmetricFunction R ≃ₐ[R] MvPolynomial ℕ+ R :=
  AlgEquiv.refl

variable {R : Type*} [CommSemiring R]

/-- The elementary family, with the unit in degree zero. -/
def e (n : ℕ) : SymmetricFunction R :=
  if hn : 0 < n then (polynomialEquiv R).symm (MvPolynomial.X ⟨n, hn⟩) else 1

@[simp] theorem e_zero : e (R := R) 0 = 1 := by
  simp [e]

/-- Positive elementary functions correspond exactly to polynomial variables. -/
@[simp] theorem polynomialEquiv_e (i : ℕ+) :
    polynomialEquiv R (e (i : ℕ)) = MvPolynomial.X i := by
  rcases i with ⟨i, hi⟩
  simp [e, hi]

@[simp] theorem polynomialEquiv_symm_X (i : ℕ+) :
    (polynomialEquiv R).symm (MvPolynomial.X i) = e (i : ℕ) := by
  rcases i with ⟨i, hi⟩
  simp [e, hi]

@[simp] theorem polynomialEquiv_e_succ (n : ℕ) :
    polynomialEquiv R (e (n + 1)) = MvPolynomial.X ⟨n + 1, Nat.succ_pos n⟩ :=
  polynomialEquiv_e ⟨n + 1, Nat.succ_pos n⟩

variable {A : Type*} [CommSemiring A] [Algebra R A]

/-- Evaluate by prescribing the images of the positive elementary generators. -/
def eval (x : ℕ+ → A) : SymmetricFunction R →ₐ[R] A :=
  (MvPolynomial.aeval x).comp (polynomialEquiv R).toAlgHom

@[simp] theorem eval_e (x : ℕ+ → A) (i : ℕ+) :
    eval x (e (R := R) (i : ℕ)) = x i := by
  simp [eval]

@[simp] theorem eval_e_zero (x : ℕ+ → A) : eval x (e (R := R) 0) = 1 := by
  simp

@[simp] theorem eval_e_succ (x : ℕ+ → A) (n : ℕ) :
    eval x (e (R := R) (n + 1)) = x ⟨n + 1, Nat.succ_pos n⟩ :=
  eval_e x ⟨n + 1, Nat.succ_pos n⟩

@[simp] theorem eval_algebraMap (x : ℕ+ → A) (r : R) :
    eval x (algebraMap R (SymmetricFunction R) r) = algebraMap R A r :=
  (eval x).commutes r

/-- Algebra maps are determined by their values on positive elementary functions. -/
@[ext high + 3] theorem algHom_ext {f g : SymmetricFunction R →ₐ[R] A}
    (h : ∀ i : ℕ+, f (e (i : ℕ)) = g (e (i : ℕ))) : f = g := by
  have h' : f.comp (polynomialEquiv R).symm.toAlgHom =
      g.comp (polynomialEquiv R).symm.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa using h i
  ext p
  simpa using AlgHom.congr_fun h' (polynomialEquiv R p)

/-- Evaluation is the unique algebra map with the specified generator images. -/
theorem eval_unique (f : SymmetricFunction R →ₐ[R] A) :
    eval (fun i : ℕ+ => f (e (i : ℕ))) = f := by
  apply algHom_ext
  simp

/-- The universal property of the polynomial presentation, with no restrictions
on the characteristic or torsion of the target algebra. -/
def evalEquiv : (ℕ+ → A) ≃ (SymmetricFunction R →ₐ[R] A) where
  toFun := eval
  invFun f i := f (e (i : ℕ))
  left_inv x := by funext i; exact eval_e x i
  right_inv := eval_unique

@[simp] theorem eval_self :
    eval (fun i : ℕ+ => e (R := R) (i : ℕ)) = AlgHom.id R (SymmetricFunction R) :=
  eval_unique (AlgHom.id R (SymmetricFunction R))

theorem comp_eval {B : Type*} [CommSemiring B] [Algebra R B]
    (f : A →ₐ[R] B) (x : ℕ+ → A) :
    f.comp (eval x) = eval (fun i => f (x i)) := by
  apply algHom_ext
  simp

/-- Induction using constants, sums, and multiplication by positive elementary
generators. This avoids exposing polynomial constructors in downstream proofs. -/
@[elab_as_elim] theorem induction_on {P : SymmetricFunction R → Prop}
    (f : SymmetricFunction R)
    (C : ∀ r, P (algebraMap R (SymmetricFunction R) r))
    (add : ∀ f g, P f → P g → P (f + g))
    (mul_e : ∀ f (i : ℕ+), P f → P (f * e (i : ℕ))) : P f := by
  suffices h : ∀ p, P ((polynomialEquiv R).symm p) by
    simpa using h (polynomialEquiv R f)
  intro p
  induction p using MvPolynomial.induction_on with
  | C r =>
    change P ((polynomialEquiv R).symm (algebraMap R (MvPolynomial ℕ+ R) r))
    rw [AlgEquiv.commutes]
    exact C r
  | add p q hp hq => simpa using add _ _ hp hq
  | mul_X p i hp => simpa using mul_e _ i hp

section Examples

-- These checks deliberately prevent unfolding the public type.
attribute [local irreducible] SymmetricFunction

example (x : ℕ+ → A) :
    eval x (e (R := R) 0 + e 2 * e 1) = 1 + x 2 * x 1 := by
  simp

example {S : Type*} [CommRing S] (r : S) (f g : SymmetricFunction S) :
    r • (f - g) = algebraMap S (SymmetricFunction S) r * f -
      algebraMap S (SymmetricFunction S) r * g := by
  rw [Algebra.smul_def, mul_sub]

example (f : SymmetricFunction R →ₐ[R] A)
    (h : ∀ i : ℕ+, f (e (i : ℕ)) = 0) : f = eval (fun _ => 0) := by
  ext i
  simpa using h i

end Examples

end

end SymmetricFunction
