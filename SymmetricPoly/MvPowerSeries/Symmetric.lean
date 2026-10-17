import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Logic.Equiv.Fintype

import SymmetricPoly.Finsupp.SymmetricAction

noncomputable section

namespace MvPowerSeries

attribute [local instance] Finsupp.comapSMul Finsupp.comapMulAction
  Finsupp.comapDistribMulAction

section SymmetricAction

variable {σ R : Type*} [CommSemiring R]
/-- There is a permutation group action on `MvPowerSeries` that is compatible with the
power series ring operations. Enable it locally when using action notation. -/
@[instance_reducible]
def permAlgAction : MulSemiringAction (Equiv.Perm σ) (MvPowerSeries σ R) where
  smul e p := rename e p
  mul_smul e₁ e₂ p := by
    change rename (e₁ * e₂) p = rename e₁ (rename e₂ p)
    rw [rename_rename]
    simp only [Equiv.Perm.coe_mul]
  one_smul p := by
    exact rename_id_apply p
  smul_zero e := (rename e).map_zero
  smul_add e := (rename e).map_add
  smul_one e := (rename e).map_one
  smul_mul e := (rename e).map_mul

attribute [local instance] permAlgAction

/-- The permutation action on `MvPowerSeries` commutes with scalar multiplication. -/
local instance permSMulCommClass : SMulCommClass (Equiv.Perm σ) R (MvPowerSeries σ R) where
  smul_comm e := by
    intro r p
    change rename e (r • p) = r • rename e p
    simp only [map_smul]

/-- Bijectively renaming the variables in a power series transforms the coefficients
  in the expected way. -/
theorem renameEquiv_coeff (e : σ ≃ τ) (p : MvPowerSeries σ R) {m : τ →₀ ℕ} :
    coeff m (rename e p) = coeff (Finsupp.equivMapDomain e.symm m) p := by
    rw [coeff_rename, Finsupp.equivMapDomain_eq_mapDomain]
    apply Finset.sum_eq_single (Finsupp.mapDomain (↑e.symm) m)
    · intro b hb hne
      simp only [Set.Finite.mem_toFinset] at hb
      exact absurd (Finsupp.mapDomain_injective e.injective
        (hb.trans (by simp [← Finsupp.mapDomain_comp]))) hne
    · intro h
      simp only [Set.Finite.mem_toFinset] at h
      exact absurd (by simp [← Finsupp.mapDomain_comp]) h

@[simp]
theorem perm_coeff (e : Equiv.Perm σ) (p : MvPowerSeries σ R) {m : σ →₀ ℕ} :
    coeff m (e • p) = coeff (e⁻¹ • m) p := by
    change coeff m (rename e p) = coeff (Finsupp.mapDomain e.symm m) p
    rw [renameEquiv_coeff, Finsupp.equivMapDomain_eq_mapDomain]

theorem perm_coeff' (e : Equiv.Perm σ) (p : MvPowerSeries σ R) {m : σ →₀ ℕ} :
  coeff (e • m) (e • p) = coeff m p := by simp

end SymmetricAction

/-- A power series is symmetric if every permutation of its variables preserves it. -/
def IsSymmetric [CommSemiring R] (p : MvPowerSeries σ R) : Prop :=
  ∀ e : Equiv.Perm σ, rename e p = p

section SymmetricSubalgebra

attribute [local instance] permAlgAction permSMulCommClass

/-- The subalgebra of symmetric power series are those that are invariant under the
  permutation group action. -/
def symmetricSubalgebra (σ R : Type*) [CommSemiring R] : Subalgebra R (MvPowerSeries σ R) :=
  FixedPoints.subalgebra R (MvPowerSeries σ R) (Equiv.Perm σ)

@[simp]
theorem mem_symmetricSubalgebra {σ R : Type*} [CommSemiring R]
    (f : MvPowerSeries σ R) :
    f ∈ symmetricSubalgebra σ R ↔ IsSymmetric f :=
  Iff.rfl

/-- The coefficients of a symmetric series are invariant under reindexing exponents. -/
@[simp]
theorem coeff_equivMapDomain_of_isSymmetric {σ R : Type*} [CommSemiring R]
    (e : Equiv.Perm σ) (m : σ →₀ ℕ)
    (f : MvPowerSeries σ R) (hf : IsSymmetric f) :
    coeff (Finsupp.equivMapDomain e m) f = coeff m f := by
  nth_rw 1 [← hf e]
  rw [renameEquiv_coeff, ← Finsupp.equivMapDomain_trans, Equiv.self_trans_symm,
    Finsupp.equivMapDomain_refl]

@[simp]
theorem coeff_smul_monomial {σ R : Type*} [CommSemiring R] (e : Equiv.Perm σ) (m : σ →₀ ℕ)
    (f : MvPowerSeries σ R) (hf : IsSymmetric f) :
    coeff (e • m) f = coeff m f := by
  change coeff (Finsupp.mapDomain e m) f = _
  rw [← Finsupp.equivMapDomain_eq_mapDomain]
  exact coeff_equivMapDomain_of_isSymmetric e m f hf

variable {σ R : Type*} [CommSemiring R]

theorem isSymmetric_C (r : R) :
    IsSymmetric (C r : MvPowerSeries σ R) := by
  intro e
  exact rename_C e r

theorem isSymmetric_one : IsSymmetric (1 : MvPowerSeries σ R) := isSymmetric_C 1

theorem isSymmetric_zero : IsSymmetric (0 : MvPowerSeries σ R) := by
  have h : (0 : MvPowerSeries σ R) = C 0 := by simp
  rw [h]
  exact isSymmetric_C 0

end SymmetricSubalgebra
end MvPowerSeries
