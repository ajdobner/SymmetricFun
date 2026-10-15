import SymmetricFunctions.Omega
import SymmetricFunctions.PowerSum
import SymmetricFunctions.BaseChange
import Mathlib.RingTheory.HopfAlgebra.Basic

/-! # The standard Hopf maps on symmetric functions -/

namespace SymmetricFunction

noncomputable section

open Finset
open scoped TensorProduct

variable {R : Type*} [CommRing R]

/-- Comultiplication for addition of alphabets. -/
def comultiplication : SymmetricFunction R →ₐ[R]
    SymmetricFunction R ⊗[R] SymmetricFunction R :=
  eval (fun n : ℕ+ => ∑ ij ∈ antidiagonal (n : ℕ), e ij.1 ⊗ₜ[R] e ij.2)

@[simp] theorem comultiplication_e (n : ℕ) :
    comultiplication (e (R := R) n) =
      ∑ ij ∈ antidiagonal n, e ij.1 ⊗ₜ[R] e ij.2 := by
  cases n <;> simp [comultiplication, Algebra.TensorProduct.one_def]

/-- The empty-alphabet counit. -/
def counit : SymmetricFunction R →ₐ[R] R := eval (fun _ : ℕ+ => 0)

@[simp] theorem counit_e (n : ℕ) : counit (e (R := R) n) = if n = 0 then 1 else 0 := by
  cases n <;> simp [counit]

/-- The antipode sends e n to the signed complete function. -/
def antipode : SymmetricFunction R →ₐ[R] SymmetricFunction R :=
  eval (fun n : ℕ+ => (-1 : R) ^ (n : ℕ) • h n)

@[simp] theorem antipode_e (n : ℕ) :
    antipode (e (R := R) n) = (-1 : R)^n • h n := by
  cases n <;> simp [antipode]

private theorem sum_antidiagonal_assoc {A : Type*} [AddCommMonoid A] (f : ℕ → ℕ → ℕ → A) (n : ℕ) :
    (∑ ij ∈ antidiagonal n, ∑ ab ∈ antidiagonal ij.1, f ab.1 ab.2 ij.2) =
      ∑ ij ∈ antidiagonal n, ∑ ab ∈ antidiagonal ij.2, f ij.1 ab.1 ab.2 := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij'
    (fun x _ => ⟨(x.2.1, x.2.2 + x.1.2), (x.2.2, x.1.2)⟩)
    (fun x _ => ⟨(x.1.1 + x.2.1, x.2.2), (x.1.1, x.2.1)⟩) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rcases x with ⟨⟨i, j⟩, ⟨a, b⟩⟩
    simp only [Finset.mem_sigma, Finset.mem_antidiagonal] at hx ⊢
    constructor
    · omega
    · trivial
  · intro x hx
    rcases x with ⟨⟨i, j⟩, ⟨a, b⟩⟩
    simp only [Finset.mem_sigma, Finset.mem_antidiagonal] at hx ⊢
    constructor
    · omega
    · trivial
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_antidiagonal] at hx
    rcases x with ⟨⟨i, j⟩, ⟨a, b⟩⟩
    simp only [Sigma.mk.inj_iff, Prod.mk.injEq, heq_eq_eq]
    simp_all
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_antidiagonal] at hx
    rcases x with ⟨⟨i, j⟩, ⟨a, b⟩⟩
    simp only [Sigma.mk.inj_iff, Prod.mk.injEq, heq_eq_eq]
    simp_all
  · intro x hx
    rfl

theorem comultiplication_coassoc :
    (Algebra.TensorProduct.assoc R R R
      (SymmetricFunction R) (SymmetricFunction R) (SymmetricFunction R)).toAlgHom.comp
      ((Algebra.TensorProduct.map comultiplication (AlgHom.id R (SymmetricFunction R))).comp
        comultiplication) =
      (Algebra.TensorProduct.map (AlgHom.id R (SymmetricFunction R)) comultiplication).comp
        comultiplication := by
  apply algHom_ext
  intro n
  simp only [AlgHom.comp_apply, comultiplication_e, map_sum, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, TensorProduct.sum_tmul, TensorProduct.tmul_sum, AlgEquiv.coe_toAlgHom,
    Algebra.TensorProduct.assoc_tmul]
  exact sum_antidiagonal_assoc
    (fun i j k => e (R := R) i ⊗ₜ[R] (e j ⊗ₜ[R] e k)) n

theorem counit_left :
    (Algebra.TensorProduct.map counit (AlgHom.id R (SymmetricFunction R))).comp comultiplication =
      (Algebra.TensorProduct.lid R (SymmetricFunction R)).symm.toAlgHom := by
  apply algHom_ext
  intro n
  simp only [AlgHom.comp_apply, comultiplication_e, map_sum, Algebra.TensorProduct.map_tmul,
    counit_e, AlgHom.id_apply, AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.lid_symm_apply]
  rw [Finset.sum_eq_single (0, (n : ℕ))]
  · simp
  · intro ij hij hne
    have hp := Finset.mem_antidiagonal.mp hij
    have hi : ij.1 ≠ 0 := by intro hi; apply hne; ext <;> omega
    simp [hi]
  · simp

theorem counit_right :
    (Algebra.TensorProduct.map (AlgHom.id R (SymmetricFunction R)) counit).comp comultiplication =
      (Algebra.TensorProduct.rid R R (SymmetricFunction R)).symm.toAlgHom := by
  apply algHom_ext
  intro n
  simp only [AlgHom.comp_apply, comultiplication_e, map_sum, Algebra.TensorProduct.map_tmul,
    counit_e, AlgHom.id_apply, AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.rid_symm_apply]
  rw [Finset.sum_eq_single ((n : ℕ), 0)]
  · simp
  · intro ij hij hne
    have hp := Finset.mem_antidiagonal.mp hij
    have hi : ij.2 ≠ 0 := by intro hi; apply hne; ext <;> omega
    simp [hi]
  · simp

theorem comultiplication_cocomm :
    (Algebra.TensorProduct.comm R (SymmetricFunction R) (SymmetricFunction R)).toAlgHom.comp
      comultiplication = comultiplication := by
  apply algHom_ext
  intro n
  simp only [AlgHom.comp_apply, comultiplication_e, map_sum, AlgEquiv.coe_toAlgHom,
    Algebra.TensorProduct.comm_tmul]
  exact Finset.Nat.sum_antidiagonal_swap
    (f := fun ij : ℕ × ℕ => e (R := R) ij.1 ⊗ₜ[R] e ij.2)

theorem antipode_left :
    (Algebra.TensorProduct.lift antipode (AlgHom.id R (SymmetricFunction R))
      (fun _ _ => Commute.all _ _)).comp comultiplication =
        (Algebra.ofId R (SymmetricFunction R)).comp counit := by
  apply algHom_ext
  intro n
  simp only [AlgHom.comp_apply, comultiplication_e, map_sum, Algebra.TensorProduct.lift_tmul,
    antipode_e, AlgHom.id_apply, smul_mul_assoc, counit_e]
  rw [h_e_convolution_signed]
  simp [n.ne_zero]

theorem antipode_right :
    (Algebra.TensorProduct.lift (AlgHom.id R (SymmetricFunction R)) antipode
      (fun _ _ => Commute.all _ _)).comp comultiplication =
        (Algebra.ofId R (SymmetricFunction R)).comp counit := by
  apply algHom_ext
  intro n
  simp only [AlgHom.comp_apply, comultiplication_e, map_sum, Algebra.TensorProduct.lift_tmul,
    antipode_e, AlgHom.id_apply, mul_smul_comm, counit_e]
  rw [e_h_convolution_signed]
  simp [n.ne_zero]

/-- The standard bialgebra, whose elementary generators have the convolution coproduct. -/
instance : Bialgebra R (SymmetricFunction R) :=
  Bialgebra.ofAlgHom comultiplication counit comultiplication_coassoc counit_left counit_right

@[simp] theorem comulAlgHom_eq : Bialgebra.comulAlgHom R (SymmetricFunction R) =
    comultiplication := rfl

@[simp] theorem counitAlgHom_eq : Bialgebra.counitAlgHom R (SymmetricFunction R) = counit := rfl

/-- Both integral convolution identities give the standard Hopf algebra. -/
instance : HopfAlgebra R (SymmetricFunction R) :=
  HopfAlgebra.ofAlgHom antipode antipode_left antipode_right

@[simp] theorem hopfAntipode_eq : HopfAlgebra.antipode R (A := SymmetricFunction R) =
    antipode.toLinearMap := rfl

instance : Coalgebra.IsCocomm R (SymmetricFunction R) where
  comm_comp_comul := congrArg AlgHom.toLinearMap comultiplication_cocomm

section Examples

attribute [local irreducible] SymmetricFunction

example : comultiplication (e (R := R) 2) =
    1 ⊗ₜ[R] e 2 + e 1 ⊗ₜ[R] e 1 + e 2 ⊗ₜ[R] 1 := by
  simp [Finset.Nat.sum_antidiagonal_succ, add_assoc]

example : antipode (e (R := R) 2) = e 1 ^ 2 - e 2 := by
  simp [h_two]

end Examples

end

end SymmetricFunction
