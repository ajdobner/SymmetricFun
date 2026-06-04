import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import SymmetricPoly.Partition
import Mathlib.Algebra.Algebra.Subalgebra.Operations

noncomputable section


namespace MvPowerSeries

section Degrees

variable {σ : Type*} {R : Type*} [CommSemiring R]

def totalDegree (p : MvPowerSeries σ R) : ℕ∞ :=
  ⨆ (m : {m : σ →₀ ℕ // coeff m p ≠ 0}), (m.1.sum (fun _ n => n) : ℕ∞)

theorem totalDegree_C (r : R) : (C r : MvPowerSeries σ R).totalDegree = 0 := by
  sorry

theorem totalDegree_mul (p q : MvPowerSeries σ R) :
    totalDegree (p * q) ≤ totalDegree p + totalDegree q := by
  sorry

theorem totalDegree_add (p q : MvPowerSeries σ R) :
    totalDegree (p + q) ≤ max (totalDegree p) (totalDegree q) := by
  sorry

def HasBoundedDegree (p : MvPowerSeries σ R) : Prop := totalDegree p < ⊤

lemma hasBddDeg_iff_exists_bound {σ R : Type*} [CommSemiring R] (p : MvPowerSeries σ R) :
    HasBoundedDegree p ↔ ∃ (D : ℕ), ∀ m, p.coeff m ≠ 0 → m.sum (fun _ e => e) ≤ D := by sorry

theorem IsHomogeneous.hasBoundedDegree {p : MvPowerSeries σ R} (h : IsHomogeneous p d) :
    HasBoundedDegree p := by
  rw [hasBddDeg_iff_exists_bound]
  use d
  intro m hm
  sorry
end Degrees






section SymmetricAction
/- The results here use `MvPowerSeries.rename`. Ultimately this should be refactored to use facts
  about general group/monoid actions on (total) monoid algebras. -/

/-- There is a permutation group action on monomials. -/
instance permMonomialAction : DistribMulAction (Equiv.Perm σ) (σ →₀ ℕ) where
  smul e f := Finsupp.domCongr e f
  one_smul f := by
    change Finsupp.domCongr (Equiv.refl σ) f = f
    rw [Finsupp.domCongr_refl]
    simp only [AddEquiv.refl_apply]
  mul_smul e₁ e₂ f := Finsupp.equivMapDomain_trans e₂ e₁ f
  smul_add e f₁ f₂ := map_add (Finsupp.domCongr e) f₁ f₂
  smul_zero e := map_zero (Finsupp.domCongr e)

theorem monomialMultiset (e : Equiv.Perm σ) (m : σ →₀ ℕ) :
    Multiset.map (e • m) (e • m).support.val = Multiset.map m m.support.val := by
  sorry

variable {σ R : Type*} [CommSemiring R]
/-- There is a permutation group action on MvPowerSeries that is compatible with the
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

/-- Permutation group action commutes with scalar multiplication. -/
instance : SMulCommClass (Equiv.Perm σ) R (MvPowerSeries σ R) where
  smul_comm e := by
    intro r p
    change rename e (r • p) = r • rename e p
    simp only [map_smul]

/-- This theorem says that if one bijectively renames the variables in a power series,
  then the coefficients transform in the expected way. -/
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


theorem perm_coeff (e : Equiv.Perm σ) (p : MvPowerSeries σ R) {m : σ →₀ ℕ} :
    coeff m (e • p) = coeff (e.symm • m) p := by
    change coeff m (rename e p) = coeff (Finsupp.equivMapDomain e.symm m) p
    rw [renameEquiv_coeff]

end SymmetricAction

section SymmetricFunctions

def bddDegSubalgebra (σ R : Type*) [CommSemiring R] : Subalgebra R (MvPowerSeries σ R) where
  carrier := {f | HasBoundedDegree f}
  algebraMap_mem' r := by
    simp [HasBoundedDegree, algebraMap_apply, totalDegree_C]
  add_mem' ha hb := by
    rename_i f g
    exact lt_of_le_of_lt (totalDegree_add f g) (max_lt ha hb)
  mul_mem' ha hb := by
    rename_i f g
    exact lt_of_le_of_lt (totalDegree_mul f g) (WithTop.add_lt_top.mpr ⟨ha, hb⟩)

/-- The subalgebra of symmetric power series are those that are invariant under the
  permutation group action. -/
def symmSubalgebra (σ R : Type*) [CommSemiring R] : Subalgebra R (MvPowerSeries σ R) :=
  FixedPoints.subalgebra R (MvPowerSeries σ R) (Equiv.Perm σ)

def IsSymmetric [CommSemiring R] (p : MvPowerSeries σ R) := p ∈ symmSubalgebra σ R

def symmetricFunctions (σ R : Type*) [CommSemiring R] : Subalgebra R (MvPowerSeries σ R) :=
  bddDegSubalgebra σ R ⊓ symmSubalgebra σ R



section MonomialSymmetric
variable {σ R : Type*} [CommSemiring R]

def msymm (σ R : Type*) [CommSemiring R] (μ : Partition) : MvPowerSeries σ R :=
  fun (m : σ →₀ ℕ) =>
    if Multiset.map m m.support.val = μ.toMultiset then 1 else 0

theorem msymm_isHomogeneous : IsHomogeneous (msymm σ R μ) |μ| := by
  intro d hd
  have hd' : msymm σ R μ d ≠ 0 := hd
  simp only [msymm] at hd'
  split_ifs at hd' with h
  · rw [Finsupp.weight_apply]
    simp only [Pi.one_apply, smul_eq_mul, mul_one]
    rw [Finsupp.sum, Finset.sum_eq_multiset_sum, h]
    simp [Partition.toMultiset, Partition.size, Multiset.sum_coe]
  · exact absurd rfl hd'

theorem msymm_isSymmetric : IsSymmetric (msymm σ R μ) := by
  intro e
  ext m
  rw [perm_coeff]
  simp only [coeff_apply, msymm, monomialMultiset]

end MonomialSymmetric

end SymmetricFunctions

end MvPowerSeries
