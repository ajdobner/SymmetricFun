import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import SymmetricPoly.Partition
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import SymmetricPoly.MvPowerSeries.Homogeneous

noncomputable section

namespace MvPowerSeries

section SymmetricAction
/- The results here use `MvPowerSeries.rename`. Probably this should later be refactored to use
  facts about group/monoid actions on total monoid algebras. -/

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
  change Multiset.map (Finsupp.equivMapDomain e m) (Finsupp.equivMapDomain e m).support.val = _
  have h : (Finsupp.equivMapDomain e m).support = Finset.map e (m.support) := by ext a; simp
  rw [h]
  simp

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

/-- The permutation action commutes with scalar multiplication. -/
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

section SymmetricFunctions


/-- The subalgebra of symmetric power series are those that are invariant under the
  permutation group action. -/
def symmSubalgebra (σ R : Type*) [CommSemiring R] : Subalgebra R (MvPowerSeries σ R) :=
  FixedPoints.subalgebra R (MvPowerSeries σ R) (Equiv.Perm σ)

def IsSymmetric [CommSemiring R] (p : MvPowerSeries σ R) := p ∈ symmSubalgebra σ R

def symmetricFunctions (σ R : Type*) [CommSemiring R] : Subalgebra R (MvPowerSeries σ R) :=
  boundedDegreeSubalgebra σ R ⊓ symmSubalgebra σ R


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

theorem msymm_mem_symmetricFunctions : msymm σ R μ ∈ symmetricFunctions σ R := by
  constructor
  · apply mem_boundedDegreeSubalgebra_of_isHomogeneous
    exact msymm_isHomogeneous
  · exact msymm_isSymmetric

end MonomialSymmetric

section ElementarySymmetric
variable {σ R : Type*} [CommSemiring R]

def esymm (σ R : Type*) [CommSemiring R] (n : ℕ) : MvPowerSeries σ R :=
  fun c ↦ if c.support.card = n ∧ (∀ i ∈ c.support, c i = 1) then 1 else 0

theorem esymm_isSymmetric σ R [CommSemiring R] (n : ℕ) : IsSymmetric (esymm σ R n) := by
  sorry

theorem esymm_mem_symmetricFunctions : esymm σ R n ∈ symmetricFunctions σ R := by
  sorry

end ElementarySymmetric

section HomogeneousSymmetric
variable {σ R : Type*} [CommSemiring R]

def hsymm (n : ℕ) : MvPowerSeries σ R :=
  fun c ↦ if c.degree = n then 1 else 0

end HomogeneousSymmetric

end SymmetricFunctions

end MvPowerSeries
