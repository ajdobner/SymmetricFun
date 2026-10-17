import SymmetricFunctions.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Coefficient maps and integral scalar extension

Coefficient maps fix the elementary generators. Tensoring the integral form
with a commutative ring gives its symmetric-function algebra. These statements
make no assumptions about characteristic or torsion and introduce no lambda
structure on an arbitrary coefficient ring.
-/

namespace SymmetricFunction

noncomputable section

open scoped TensorProduct

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

/-- Ring maps are determined by their coefficient and elementary-generator images. -/
theorem ringHom_ext {A : Type*} [Semiring A] {f g : SymmetricFunction R →+* A}
    (hC : ∀ r, f (algebraMap R (SymmetricFunction R) r) =
      g (algebraMap R (SymmetricFunction R) r))
    (he : ∀ i : ℕ+, f (e (i : ℕ)) = g (e (i : ℕ))) : f = g := by
  ext p
  induction p using SymmetricFunction.induction_on with
  | C r => exact hC r
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_e p i hp => simp only [map_mul, hp, he i]

/-- Evaluation with an arbitrary coefficient ring homomorphism. -/
def eval₂ (φ : R →+* S) (x : ℕ+ → S) : SymmetricFunction R →+* S :=
  (MvPolynomial.eval₂Hom φ x).comp (polynomialEquiv R).toRingHom

@[simp] theorem eval₂_algebraMap (φ : R →+* S) (x : ℕ+ → S) (r : R) :
    eval₂ φ x (algebraMap R (SymmetricFunction R) r) = φ r := by
  simp [eval₂]

@[simp] theorem eval₂_e (φ : R →+* S) (x : ℕ+ → S) (i : ℕ+) :
    eval₂ φ x (e (i : ℕ)) = x i := by
  simp [eval₂]

@[simp] theorem eval₂_e_zero (φ : R →+* S) (x : ℕ+ → S) :
    eval₂ φ x (e 0) = 1 := by simp

@[simp] theorem eval₂_e_succ (φ : R →+* S) (x : ℕ+ → S) (n : ℕ) :
    eval₂ φ x (e (n + 1)) = x ⟨n + 1, Nat.succ_pos n⟩ :=
  eval₂_e φ x ⟨n + 1, Nat.succ_pos n⟩

theorem eval₂_eq_eval [Algebra R S] (x : ℕ+ → S) :
    eval₂ (algebraMap R S) x = (eval x).toRingHom := by
  apply ringHom_ext <;> intro i <;> simp

/-- Change coefficients through a ring homomorphism, fixing all elementary generators. -/
def map (φ : R →+* S) : SymmetricFunction R →+* SymmetricFunction S :=
  (polynomialEquiv S).symm.toRingHom.comp
    ((MvPolynomial.map φ).comp (polynomialEquiv R).toRingHom)

@[simp] theorem polynomialEquiv_map (φ : R →+* S) (f : SymmetricFunction R) :
    polynomialEquiv S (map φ f) = MvPolynomial.map φ (polynomialEquiv R f) := by
  simp [map]

@[simp] theorem map_algebraMap (φ : R →+* S) (r : R) :
    map φ (algebraMap R (SymmetricFunction R) r) =
      algebraMap S (SymmetricFunction S) (φ r) := by
  apply (polynomialEquiv S).injective
  simp

@[simp] theorem map_e (φ : R →+* S) (n : ℕ) : map φ (e n) = e n := by
  cases n with
  | zero => simp
  | succ n =>
    apply (polynomialEquiv S).injective
    simp only [polynomialEquiv_map, polynomialEquiv_e_succ]
    exact MvPolynomial.map_X φ (⟨n + 1, Nat.succ_pos n⟩ : ℕ+)

@[simp] theorem map_id : map (RingHom.id R) = RingHom.id (SymmetricFunction R) := by
  apply ringHom_ext <;> intro i <;> simp

@[simp] theorem map_comp (ψ : S →+* T) (φ : R →+* S) :
    map (ψ.comp φ) = (map ψ).comp (map φ) := by
  apply ringHom_ext <;> intro i <;> simp

/-- Evaluation commutes with arbitrary coefficient change. -/
theorem eval₂_map (ψ : S →+* T) (φ : R →+* S) (x : ℕ+ → T) (f : SymmetricFunction R) :
    eval₂ ψ x (map φ f) = eval₂ (ψ.comp φ) x f := by
  have h : (eval₂ ψ x).comp (map φ) = eval₂ (ψ.comp φ) x := by
    apply ringHom_ext <;> intro i <;> simp
  exact RingHom.congr_fun h f

theorem eval_map {A : Type*} [CommSemiring A] [Algebra S A]
    (φ : R →+* S) (x : ℕ+ → A) (f : SymmetricFunction R) :
    eval x (map φ f) = eval₂ ((algebraMap S A).comp φ) x f := by
  rw [← eval₂_map]
  exact RingHom.congr_fun (eval₂_eq_eval x).symm (map φ f)

/-- Naturality of evaluation under a ring homomorphism of targets. -/
theorem comp_eval₂ (ψ : S →+* T) (φ : R →+* S) (x : ℕ+ → S) :
    ψ.comp (eval₂ φ x) = eval₂ (ψ.comp φ) (fun i => ψ (x i)) := by
  apply ringHom_ext <;> intro i <;> simp

section Integral

variable (A : Type*) [CommRing A]

/-- Every coefficient ring is obtained by scalar extension from the integral form. -/
def baseChange : A ⊗[ℤ] SymmetricFunction ℤ ≃ₐ[A] SymmetricFunction A :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) (polynomialEquiv ℤ)).trans
    ((MvPolynomial.algebraTensorAlgEquiv ℤ A).trans (polynomialEquiv A).symm)

@[simp] theorem baseChange_tmul (a : A) (f : SymmetricFunction ℤ) :
    baseChange A (a ⊗ₜ[ℤ] f) = a • map (Int.castRingHom A) f := by
  simp [baseChange, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    map, MvPolynomial.algebraTensorAlgEquiv_tmul]

@[simp] theorem baseChange_one_tmul_e (n : ℕ) :
    baseChange A (1 ⊗ₜ[ℤ] e (R := ℤ) n) = e (R := A) n := by
  simp

@[simp] theorem baseChange_symm_e (n : ℕ) :
    (baseChange A).symm (e n) = 1 ⊗ₜ[ℤ] e (R := ℤ) n :=
  (baseChange A).symm_apply_eq.mpr (baseChange_one_tmul_e A n).symm

/-- Scalar extension agrees with evaluation in every commutative target algebra. -/
theorem eval_baseChange_tmul {B : Type*} [CommRing B] [Algebra A B]
    (x : ℕ+ → B) (a : A) (f : SymmetricFunction ℤ) :
    eval x (baseChange A (a ⊗ₜ[ℤ] f)) =
      algebraMap A B a * eval₂ (Int.castRingHom B) x f := by
  rw [baseChange_tmul, Algebra.smul_def, map_mul, eval_algebraMap, eval_map]
  have h : (algebraMap A B).comp (Int.castRingHom A) = Int.castRingHom B :=
    Subsingleton.elim _ _
  rw [h]

section Examples

attribute [local irreducible] SymmetricFunction

example : (baseChange A).symm (e 2 + e 1 ^ 2) =
    1 ⊗ₜ[ℤ] e (R := ℤ) 2 + (1 ⊗ₜ[ℤ] e (R := ℤ) 1) ^ 2 := by
  simp

example (φ : R →+* S) : map φ (e 0 + e 2 * e 1) = 1 + e 2 * e 1 := by
  simp

end Examples

end Integral

end

end SymmetricFunction
