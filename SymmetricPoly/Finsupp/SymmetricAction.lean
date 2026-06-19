import Mathlib.Data.Finsupp.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Group.End
import Mathlib.Data.Finsupp.Weight

import SymmetricPoly.Combinatorics.Enumerative.Partition.Basic

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
  TODO: Is it better to use the one-liner `Finsupp.comapDistribMulAction` to define this? -/
instance permAction {σ : Type*} : DistribMulAction (Equiv.Perm σ) (σ →₀ ℕ) where
  smul e f := Finsupp.domCongr e f
  one_smul f := by
    change Finsupp.domCongr (Equiv.refl σ) f = f
    rw [Finsupp.domCongr_refl]
    simp only [AddEquiv.refl_apply]
  mul_smul e₁ e₂ f := Finsupp.equivMapDomain_trans e₂ e₁ f
  smul_add e f₁ f₂ := map_add (Finsupp.domCongr e) f₁ f₂
  smul_zero e := map_zero (Finsupp.domCongr e)

def toGenericPartition (m : σ →₀ ℕ) : Nat.GenericPartition where
  parts := Multiset.map m m.support.val
  parts_pos := by
    intro x hx
    rw [Multiset.mem_map] at hx
    rcases hx with ⟨a, ha, rfl⟩
    have h_nonzero : m a ≠ 0 := Finsupp.mem_support_iff.mp ha
    exact Nat.pos_of_ne_zero h_nonzero

theorem toGenericPartition_size (m : σ →₀ ℕ) : m.toGenericPartition.size = m.weight 1 := by
  sorry

theorem embDomain_toGenericPartition (f : α ↪ β) (m : α →₀ ℕ) :
    (m.embDomain f).toGenericPartition = m.toGenericPartition := by
  unfold toGenericPartition
  simp

lemma smul_multiset_helper (e : Equiv.Perm σ) (m : σ →₀ ℕ) :
    Multiset.map (e • m) (e • m).support.val = Multiset.map m m.support.val := by
  change Multiset.map (Finsupp.equivMapDomain e m) (Finsupp.equivMapDomain e m).support.val = _
  have h : (Finsupp.equivMapDomain e m).support = Finset.map e (m.support) := by ext a; simp
  rw [h]
  simp

@[simp]
lemma toGenericPartition_smul {σ : Type*} (e : Equiv.Perm σ) (m : σ →₀ ℕ) :
  (e • m).toGenericPartition = m.toGenericPartition:= by
  apply Nat.GenericPartition.ext
  --change (Multiset.map (e • m) (e • m).support.val).sort (· ≥ ·) =
    --(Multiset.map m m.support.val).sort (· ≥ ·)
  unfold toGenericPartition
  simp only
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

lemma exists_smul_of_toGenericPartition_eq {σ : Type*} (m₁ m₂ : σ →₀ ℕ)
    (h : m₁.toGenericPartition = m₂.toGenericPartition) :
    ∃ e : Equiv.Perm σ, m₁ = e • m₂ := by
  apply finsupp_perm_of_multiset_eq m₁ m₂
  exact congrArg Nat.GenericPartition.parts h

theorem toGenericPartition_eq_iff {σ R : Type*} [CommSemiring R] (m₁ m₂ : σ →₀ ℕ) :
  m₁.toGenericPartition = m₂.toGenericPartition ↔ ∃ e : Equiv.Perm σ, m₁ = e • m₂:=
  by
  constructor
  · exact exists_smul_of_toGenericPartition_eq m₁ m₂
  · rintro ⟨e, rfl⟩
    exact toGenericPartition_smul e m₂

end Finsupp
