import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Group.Action.End
import Mathlib.Data.Finsupp.Weight

import SymmetricPoly.AllPartitions

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

-- Use the existing action on the domain only within this file.
-- It is not global because Finsupp also supports actions on its values.
attribute [local instance] comapSMul comapMulAction comapDistribMulAction

/-- The partition formed by the nonzero entries of an exponent vector. -/
def toAllPartitions (m : σ →₀ ℕ) : AllPartitions :=
  ⟨m.degree, {
    parts := Multiset.map m m.support.val
    parts_pos := by
      intro x hx
      rw [Multiset.mem_map] at hx
      rcases hx with ⟨a, ha, rfl⟩
      have h_nonzero : m a ≠ 0 := Finsupp.mem_support_iff.mp ha
      exact Nat.pos_of_ne_zero h_nonzero
    parts_sum := rfl
  }⟩

theorem toAllPartitions_size (m : σ →₀ ℕ) : m.toAllPartitions.size = m.weight 1 := by
  change m.degree = m.weight 1
  rw [degree_eq_weight_one]
  rfl

theorem embDomain_toAllPartitions (f : α ↪ β) (m : α →₀ ℕ) :
    (m.embDomain f).toAllPartitions = m.toAllPartitions := by
  apply AllPartitions.ext
  simp [toAllPartitions, AllPartitions.parts]

/-- Reindexing an exponent vector by an equivalence preserves its partition. -/
@[simp]
theorem toAllPartitions_equivMapDomain (e : σ ≃ τ) (m : σ →₀ ℕ) :
    (equivMapDomain e m).toAllPartitions = m.toAllPartitions := by
  apply AllPartitions.ext
  change Multiset.map (equivMapDomain e m) (equivMapDomain e m).support.val =
    Multiset.map m m.support.val
  have h : (Finsupp.equivMapDomain e m).support = Finset.map e (m.support) := by ext a; simp
  rw [h]
  simp [Function.comp_def]

lemma smul_multiset_helper (e : Equiv.Perm σ) (m : σ →₀ ℕ) :
    Multiset.map (e • m) (e • m).support.val = Multiset.map m m.support.val := by
  change Multiset.map (mapDomain e m) (mapDomain e m).support.val = _
  rw [← equivMapDomain_eq_mapDomain]
  exact congrArg AllPartitions.parts (toAllPartitions_equivMapDomain e m)

@[simp]
lemma toAllPartitions_smul {σ : Type*} (e : Equiv.Perm σ) (m : σ →₀ ℕ) :
    (e • m).toAllPartitions = m.toAllPartitions := by
  change (mapDomain e m).toAllPartitions = _
  rw [← equivMapDomain_eq_mapDomain, toAllPartitions_equivMapDomain]


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

lemma exists_equivMapDomain_of_toAllPartitions_eq {σ : Type*} (m₁ m₂ : σ →₀ ℕ)
    (h : m₁.toAllPartitions = m₂.toAllPartitions) :
    ∃ e : Equiv.Perm σ, m₁ = equivMapDomain e m₂ := by
  apply finsupp_perm_of_multiset_eq m₁ m₂
  exact congrArg AllPartitions.parts h

lemma exists_smul_of_toAllPartitions_eq {σ : Type*} (m₁ m₂ : σ →₀ ℕ)
    (h : m₁.toAllPartitions = m₂.toAllPartitions) :
    ∃ e : Equiv.Perm σ, m₁ = e • m₂ := by
  obtain ⟨e, he⟩ := exists_equivMapDomain_of_toAllPartitions_eq m₁ m₂ h
  refine ⟨e, ?_⟩
  change m₁ = mapDomain e m₂
  simpa only [equivMapDomain_eq_mapDomain] using he

theorem toAllPartitions_eq_iff {σ R : Type*} [CommSemiring R] (m₁ m₂ : σ →₀ ℕ) :
  m₁.toAllPartitions = m₂.toAllPartitions ↔ ∃ e : Equiv.Perm σ, m₁ = e • m₂:=
  by
  constructor
  · exact exists_smul_of_toAllPartitions_eq m₁ m₂
  · rintro ⟨e, rfl⟩
    exact toAllPartitions_smul e m₂

end Finsupp
