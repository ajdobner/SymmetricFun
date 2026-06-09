import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Logic.Equiv.Fintype
import SymmetricPoly.Partition

noncomputable section

namespace Finsupp

/-- There is a permutation group action on monomials. -/
instance : DistribMulAction (Equiv.Perm σ) (σ →₀ ℕ) where
  smul e f := Finsupp.domCongr e f
  one_smul f := by
    change Finsupp.domCongr (Equiv.refl σ) f = f
    rw [Finsupp.domCongr_refl]
    simp only [AddEquiv.refl_apply]
  mul_smul e₁ e₂ f := Finsupp.equivMapDomain_trans e₂ e₁ f
  smul_add e f₁ f₂ := map_add (Finsupp.domCongr e) f₁ f₂
  smul_zero e := map_zero (Finsupp.domCongr e)

def toPartition (m : σ →₀ ℕ) : Partition where
  parts := (Multiset.map m m.support.val).sort (· ≥ ·)
  sorted := Multiset.pairwise_sort _ _
  pos := by
    intro x hx
    rw [Multiset.mem_sort] at hx
    rw [Multiset.mem_map] at hx
    rcases hx with ⟨a, ha, rfl⟩
    have h_nonzero : m a ≠ 0 := Finsupp.mem_support_iff.mp ha
    exact Nat.pos_of_ne_zero h_nonzero

lemma smul_multiset_helper (e : Equiv.Perm σ) (m : σ →₀ ℕ) :
    Multiset.map (e • m) (e • m).support.val = Multiset.map m m.support.val := by
  change Multiset.map (Finsupp.equivMapDomain e m) (Finsupp.equivMapDomain e m).support.val = _
  have h : (Finsupp.equivMapDomain e m).support = Finset.map e (m.support) := by ext a; simp
  rw [h]
  simp

@[simp]
lemma toPartition_smul {σ : Type*} (e : Equiv.Perm σ) (m : σ →₀ ℕ) :
  (e • m).toPartition = m.toPartition:= by
  apply Partition.ext
  change (Multiset.map (e • m) (e • m).support.val).sort (· ≥ ·) =
    (Multiset.map m m.support.val).sort (· ≥ ·)
  rw [smul_multiset_helper e m]

lemma toPartition_perm (m : σ →₀ ℕ) : m.toPartition.parts.Perm (Multiset.map m m.support.val).toList := by
  sorry

lemma exists_smul_of_toPartition_eq {σ : Type*} (m₁ m₂ : σ →₀ ℕ)
    (h : m₁.toPartition = m₂.toPartition) :
    ∃ e : Equiv.Perm σ, e • m₁ = m₂ := by
  have h' : (Multiset.map m₁ m₁.support.val).toList.Perm (Multiset.map m₂ m₂.support.val).toList := by
    transitivity m₁.toPartition.parts
    · symm
      apply toPartition_perm
    transitivity m₂.toPartition.parts
    · simp [h]
    apply toPartition_perm
  sorry


theorem toPartition_eq_iff {σ R : Type*} [CommSemiring R] (m₁ m₂ : σ →₀ ℕ) :
  m₁.toPartition = m₂.toPartition ↔ ∃ e : Equiv.Perm σ, e • m₁ = m₂:=
  by
  constructor
  · exact exists_smul_of_toPartition_eq m₁ m₂
  · rintro ⟨e, rfl⟩
    exact (toPartition_smul e m₁).symm


end Finsupp

namespace MvPowerSeries

section SymmetricAction
/- The results here use `MvPowerSeries.rename`. Probably this should later be refactored to use
  facts about group/monoid actions on total monoid algebras. -/


-- lemma test' {α : Type*} (A B : Finset α) (f : ↑A ≃ ↑B) :
--   ∃ e : Equiv.Perm α, ∀ a : ↑A, e ↑a = ↑(f a) := by
--   classical
--   -- Construct the full permutation directly from f
--   use Equiv.extendSubtype f
--   intro a
--   -- Prove it acts exactly like f on elements inside A
--   exact Equiv.extendSubtype_apply_of_mem f ↑a a.property



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
lemma isSymmetric_iff_mem_symmetricSubalgebra {σ R : Type*} [CommSemiring R]
    (f : MvPowerSeries σ R) :
    IsSymmetric f ↔ f ∈ symmetricSubalgebra σ R :=
  Iff.rfl

@[simp]
lemma coeff_smul_monomial {σ R : Type*} [CommSemiring R] (e : Equiv.Perm σ) (m : σ →₀ ℕ)
    (f : MvPowerSeries σ R) (hf : IsSymmetric f) :
     coeff (e • m) f = coeff m f := by
  nth_rw 1 [← hf e]
  simp

end SymmetricSubalgebra
end MvPowerSeries
