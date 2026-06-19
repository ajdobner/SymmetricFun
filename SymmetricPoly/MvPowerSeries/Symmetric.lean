import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Logic.Equiv.Fintype

import SymmetricPoly.Finsupp.SymmetricAction

noncomputable section

namespace MvPowerSeries

section SymmetricAction
/- The results here use `MvPowerSeries.rename`. Probably this should later be refactored to use
  facts about group/monoid actions on total monoid algebras. -/

variable {σ R : Type*} [CommSemiring R]
/-- There is a permutation group action on `MvPowerSeries` that is compatible with the
  power series ring operations. -/
instance permAlgAction : MulSemiringAction (Equiv.Perm σ) (MvPowerSeries σ R) where
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

/-- The permutation action on `MvPowerSeries` commutes with scalar multiplication. -/
instance : SMulCommClass (Equiv.Perm σ) R (MvPowerSeries σ R) where
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
        (hb.trans (by simp [← Finsupp.mapDomain_comp, Equiv.self_comp_symm]))) hne
    · intro h
      simp only [Set.Finite.mem_toFinset] at h
      exact absurd (by simp [← Finsupp.mapDomain_comp, Equiv.self_comp_symm]) h

@[simp]
theorem perm_coeff (e : Equiv.Perm σ) (p : MvPowerSeries σ R) {m : σ →₀ ℕ} :
    coeff m (e • p) = coeff (e⁻¹ • m) p := by
    change coeff m (rename e p) = coeff (Finsupp.equivMapDomain e.symm m) p
    rw [renameEquiv_coeff]

theorem perm_coeff' (e : Equiv.Perm σ) (p : MvPowerSeries σ R) {m : σ →₀ ℕ} :
  coeff (e • m) (e • p) = coeff m p := by simp

end SymmetricAction

section SymmetricSubalgebra
/-- The subalgebra of symmetric power series are those that are invariant under the
  permutation group action. -/
def symmetricSubalgebra (σ R : Type*) [CommSemiring R] : Subalgebra R (MvPowerSeries σ R) :=
  FixedPoints.subalgebra R (MvPowerSeries σ R) (Equiv.Perm σ)

def IsSymmetric [CommSemiring R] (p : MvPowerSeries σ R) := ∀ e : Equiv.Perm σ, e • p = p

@[simp]
theorem mem_symmetricSubalgebra {σ R : Type*} [CommSemiring R]
    (f : MvPowerSeries σ R) :
    f ∈ symmetricSubalgebra σ R ↔ IsSymmetric f :=
  Iff.rfl

@[simp]
theorem coeff_smul_monomial {σ R : Type*} [CommSemiring R] (e : Equiv.Perm σ) (m : σ →₀ ℕ)
    (f : MvPowerSeries σ R) (hf : IsSymmetric f) :
     coeff (e • m) f = coeff m f := by
  nth_rw 1 [← hf e]
  simp

variable {σ R : Type*} [CommSemiring R]

theorem isSymmetric_C (r : R) :
    IsSymmetric (C r : MvPowerSeries σ R) := by
  sorry

theorem isSymmetric_one : IsSymmetric (1 : MvPowerSeries σ R) := isSymmetric_C 1

theorem isSymmetric_zero : IsSymmetric (0 : MvPowerSeries σ R) := by
  have h : (0 : MvPowerSeries σ R) = C 0 := by simp
  rw [h]
  exact isSymmetric_C 0

end SymmetricSubalgebra
end MvPowerSeries
