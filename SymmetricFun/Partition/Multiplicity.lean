module

public import SymmetricFun.Partition.IntegerPartition
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.PNat.Basic

/-!
# Partitions and multiplicities of positive parts

`IntegerPartition.multiplicitiesEquiv` identifies a partition with the finitely
supported function recording how many times each positive part occurs.
The size of the partition is the weight of this function, giving part `i`
weight `i`.
-/

@[expose] public section
noncomputable section

namespace IntegerPartition

/-- The number of occurrences of each positive part in a partition. -/
def multiplicities (μ : IntegerPartition) : ℕ+ →₀ ℕ :=
  μ.parts.toFinsupp.subtypeDomain (fun i : ℕ => 0 < i)

@[simp]
theorem multiplicities_apply (μ : IntegerPartition) (i : ℕ+) :
    μ.multiplicities i = μ.parts.count (i : ℕ) := rfl

theorem multiplicities_injective : Function.Injective multiplicities := by
  intro μ ν h
  apply IntegerPartition.ext
  apply Multiset.ext.mpr
  intro i
  by_cases hi : 0 < i
  · exact DFunLike.congr_fun h ⟨i, hi⟩
  · have hμ : i ∉ μ.parts := fun h => hi (μ.parts_pos h)
    have hν : i ∉ ν.parts := fun h => hi (ν.parts_pos h)
    simp [Multiset.count_eq_zero.mpr hμ, Multiset.count_eq_zero.mpr hν]

/-- Form a partition with `a i` copies of each positive integer `i`. -/
def ofMultiplicities (a : ℕ+ →₀ ℕ) : IntegerPartition :=
  ⟨(a.toMultiset.map PNat.val).sum,
    { parts := a.toMultiset.map PNat.val
      parts_pos := by
        intro i hi
        obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hi
        exact j.pos
      parts_sum := rfl }⟩

@[simp]
theorem parts_ofMultiplicities (a : ℕ+ →₀ ℕ) :
    (ofMultiplicities a).parts = a.toMultiset.map PNat.val := rfl

@[simp]
theorem multiplicities_ofMultiplicities (a : ℕ+ →₀ ℕ) :
    (ofMultiplicities a).multiplicities = a := by
  ext i
  rw [multiplicities_apply, parts_ofMultiplicities,
    Multiset.count_map_eq_count' _ _ PNat.coe_injective, Finsupp.count_toMultiset]

@[simp]
theorem ofMultiplicities_multiplicities (μ : IntegerPartition) :
    ofMultiplicities μ.multiplicities = μ :=
  multiplicities_injective (multiplicities_ofMultiplicities μ.multiplicities)

/-- Partitions of arbitrary size are equivalent to multiplicities of positive parts. -/
def multiplicitiesEquiv : IntegerPartition ≃ (ℕ+ →₀ ℕ) where
  toFun := multiplicities
  invFun := ofMultiplicities
  left_inv := ofMultiplicities_multiplicities
  right_inv := multiplicities_ofMultiplicities

@[simp]
theorem multiplicitiesEquiv_apply (μ : IntegerPartition) :
    multiplicitiesEquiv μ = μ.multiplicities := rfl

@[simp]
theorem multiplicitiesEquiv_symm_apply (a : ℕ+ →₀ ℕ) :
    multiplicitiesEquiv.symm a = ofMultiplicities a := rfl

@[simp]
theorem size_ofMultiplicities (a : ℕ+ →₀ ℕ) :
    (ofMultiplicities a).size = Finsupp.weight PNat.val a := by
  change (a.toMultiset.map PNat.val).sum = Finsupp.weight PNat.val a
  rw [Finsupp.toMultiset_map, Finsupp.sum_toMultiset,
    Finsupp.sum_mapDomain_index_inj PNat.coe_injective]
  rfl

@[simp]
theorem weight_multiplicities (μ : IntegerPartition) :
    Finsupp.weight PNat.val μ.multiplicities = μ.size := by
  rw [← size_ofMultiplicities, ofMultiplicities_multiplicities]

end IntegerPartition
