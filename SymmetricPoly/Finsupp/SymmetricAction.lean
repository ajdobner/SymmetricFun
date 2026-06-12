import Mathlib.Data.Finsupp.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Group.End

import SymmetricPoly.Partition

noncomputable section

lemma fintype_card_eq_finset {α : Type*} (f : α → Prop) [DecidablePred f] (A : Finset α) :
  Fintype.card { a : A // f a } = (Finset.filter f A).card := by
  let e : { a : A // f a } ≃ ↥(Finset.filter f A) := {
    toFun := fun ⟨⟨x, hA⟩, hf⟩ =>
      ⟨x, Finset.mem_filter.mpr ⟨hA, hf⟩⟩
    invFun := fun ⟨x, hAf⟩ =>
      ⟨⟨x, (Finset.mem_filter.mp hAf).1⟩, (Finset.mem_filter.mp hAf).2⟩
    left_inv := fun ⟨⟨x, hA⟩, hf⟩ => rfl
    right_inv := fun ⟨x, hAf⟩ => rfl
  }
  have h : Fintype.card { a : A // f a } = Fintype.card ↥(Finset.filter f A) := Fintype.card_congr e
  rw [h]
  simp

namespace Finsupp

/-- There is a permutation group action on monomials.
  TODO: This can be constructed by simply lifting the `Equiv.Perm σ` action on the domain. -/
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

theorem toPartition_toMultiset (m : σ →₀ ℕ) :
    m.toPartition.toMultiset = Multiset.map m m.support.val := by
  ext x
  rw [toPartition, Partition.toMultiset]
  simp

theorem embDomain_toPartition' (f : α ↪ β) (m : α →₀ ℕ) :
    Multiset.map (m.embDomain f) (m.embDomain f).support.val = Multiset.map m m.support.val := by
  simp

theorem embDomain_toPartition (f : α ↪ β) (m : α →₀ ℕ) :
    (m.embDomain f).toPartition = m.toPartition := by
  apply Partition.ext'.mpr
  rw [toPartition_toMultiset, toPartition_toMultiset]
  exact embDomain_toPartition' f m

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



theorem finsupp_perm_of_multiset_eq {α β : Type*} [Zero β]
    (f g : α →₀ β) (h : Multiset.map f f.support.val = Multiset.map g g.support.val) :
    ∃ e : Equiv.Perm α, f = g.equivMapDomain e := by
  classical
  have h_fiber (c : β) :
      Fintype.card {a : f.support // f a = c} = Fintype.card {a : g.support // g a = c} := by
    rw [fintype_card_eq_finset (fun a => f a = c) f.support,
        fintype_card_eq_finset (fun a => g a = c) g.support]
    apply Multiset.ext.mp at h
    let h := h c
    rw [Multiset.count_map, Multiset.count_map] at h
    simp_rw [eq_comm (a := c)] at h
    exact h
  let equiv_family : ∀ c : β, {a : f.support // f a = c} ≃ {a : g.support // g a = c} :=
    fun c => Fintype.equivOfCardEq (h_fiber c)
  -- Construct an equivalence on the supports by piecing together the equivalences on the fibers.
  let e_small : f.support ≃ g.support := Equiv.ofFiberEquiv equiv_family
  have he_small : ∀ a : f.support, f a = g (e_small a) := by
    intro a
    exact (Equiv.ofFiberEquiv_map equiv_family a).symm
  -- Extend equivalence to the whole type α.
  let e_large : α ≃ α := Equiv.extendSubtype e_small
  have h_e_large : ∀ a : α, f a = g (e_large a) := by
    intro a
    by_cases ha : a ∈ f.support
    · rw [Equiv.extendSubtype_apply_of_mem e_small a ha]
      exact he_small ⟨a, ha⟩
    · transitivity 0
      · exact notMem_support_iff.mp ha
      · symm
        exact notMem_support_iff.mp (Equiv.extendSubtype_not_mem e_small a ha)
  use e_large.symm
  ext a
  simp only [Finsupp.equivMapDomain_apply, h_e_large a, Equiv.symm_symm]

lemma exists_smul_of_toPartition_eq {σ : Type*} (m₁ m₂ : σ →₀ ℕ)
    (h : m₁.toPartition = m₂.toPartition) :
    ∃ e : Equiv.Perm σ, m₁ = e • m₂ := by
  have h_multiset : Multiset.map m₁ m₁.support.val = Multiset.map m₂ m₂.support.val := by
    rw [← toPartition_toMultiset m₁, ← toPartition_toMultiset m₂, h]
  apply finsupp_perm_of_multiset_eq m₁ m₂ at h_multiset
  change ∃ e : Equiv.Perm σ, m₁ = m₂.equivMapDomain e
  exact h_multiset

theorem toPartition_eq_iff {σ R : Type*} [CommSemiring R] (m₁ m₂ : σ →₀ ℕ) :
  m₁.toPartition = m₂.toPartition ↔ ∃ e : Equiv.Perm σ, m₁ = e • m₂:=
  by
  constructor
  · exact exists_smul_of_toPartition_eq m₁ m₂
  · rintro ⟨e, rfl⟩
    exact toPartition_smul e m₂

end Finsupp
