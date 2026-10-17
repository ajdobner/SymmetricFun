module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Finsupp.Weight
public import SymmetricFun.Partition.AllPartitions

/-!
# Exponent vectors and partitions

The nonzero entries of a finitely supported exponent vector form a partition.
Two exponent vectors give the same partition exactly when they differ by a
permutation of their indices.
-/

@[expose] public section
noncomputable section

namespace Finsupp

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
  simpa only [embDomain_eq_mapDomain, equivMapDomain_eq_mapDomain, Equiv.coe_toEmbedding]
    using embDomain_toAllPartitions e.toEmbedding m

/-- Finitely supported functions with the same multiset of nonzero values differ by
a permutation of their indices. -/
theorem exists_equivMapDomain_of_multiset_eq {α β : Type*} [Zero β]
    (f g : α →₀ β) (h : Multiset.map f f.support.val = Multiset.map g g.support.val) :
    ∃ e : Equiv.Perm α, f = g.equivMapDomain e := by
  classical
  have h_fiber (c : β) :
      Fintype.card {a : f.support // f a = c} = Fintype.card {a : g.support // g a = c} := by
    simp only [Fintype.card_subtype, Finset.univ_eq_attach,
      Finset.filter_attach (fun a => f a = c), Finset.filter_attach (fun a => g a = c),
      Finset.card_map, Finset.card_attach]
    simpa only [Multiset.count_map, eq_comm (a := c), Finset.card_def, Finset.filter_val]
      using congrArg (Multiset.count c) h
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
  apply exists_equivMapDomain_of_multiset_eq m₁ m₂
  exact congrArg AllPartitions.parts h

end Finsupp
