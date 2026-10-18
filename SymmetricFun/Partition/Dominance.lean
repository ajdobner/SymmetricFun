module

public import SymmetricFun.Partition.Parts
public import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram

/-!
# Dominance of partitions

`Nat.Partition.partialSum μ k` sums the first `k` parts in decreasing order, padding
with zeros. It takes a prefix of the sorted multiset of parts;
`partialSum_eq_sum_rowLen` identifies it with a sum of Young diagram row lengths.

`μ.Dominates ν` means that every partial sum of `ν` is at most the corresponding
partial sum of `μ`. This is a decidable, reflexive, transitive, antisymmetric
relation. The named `dominanceOrder` can be enabled locally when an order instance
is useful; no order instance on partitions is installed globally.

The identity `partialSum_conjugate` expresses the sum of the first `k` parts of
the conjugate as the sum of `min k i` over the original parts. Its proof counts
cells in the first `k` columns of the Young diagram, first by columns and then
by rows.
-/

@[expose] public section

open Finset

namespace YoungDiagram

/-- Rows beyond the first column have length zero. -/
lemma rowLen_eq_zero_of_colLen_le (μ : YoungDiagram) {i : ℕ} (hi : μ.colLen 0 ≤ i) :
    μ.rowLen i = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro h
  exact (not_lt_of_ge hi) (mem_iff_lt_colLen.mp (mem_iff_lt_rowLen.mpr h))

/-- Summing row lengths agrees with taking a prefix of the list of nonempty rows. -/
lemma sum_rowLen_eq_sum_take_rowLens (μ : YoungDiagram) (k : ℕ) :
    ∑ i ∈ range k, μ.rowLen i = (μ.rowLens.take k).sum := by
  have h : ∑ i ∈ range k, μ.rowLen i =
      ∑ i ∈ range (min k (μ.colLen 0)), μ.rowLen i := by
    symm
    apply sum_subset (range_mono (min_le_left _ _))
    intro i hi hnot
    apply μ.rowLen_eq_zero_of_colLen_le
    simp only [mem_range] at hi hnot
    omega
  simpa only [rowLens, ← List.map_take, List.take_range, Finset.sum_eq_multiset_sum,
    Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe] using h

/-- Count the cells in the first `k` columns by columns and by rows. -/
lemma sum_colLen_eq_sum_min_rowLen (μ : YoungDiagram) (k : ℕ) :
    ∑ j ∈ range k, μ.colLen j = ∑ i ∈ range (μ.colLen 0), min k (μ.rowLen i) := by
  have hf : (↑{c ∈ μ.cells | c.2 < k} : Set (ℕ × ℕ)).MapsTo Prod.fst
      (range (μ.colLen 0)) := by
    intro c hc
    rw [Finset.mem_coe, mem_range, ← mem_iff_lt_colLen]
    exact μ.up_left_mem le_rfl (Nat.zero_le _) (mem_filter.mp hc).1
  have hr (i : ℕ) :
      {c ∈ {c ∈ μ.cells | c.2 < k} | c.1 = i} =
        {i} ×ˢ range (min k (μ.rowLen i)) := by
    ext ⟨a, b⟩
    rcases eq_or_ne a i with rfl | h
    · simp [mem_iff_lt_rowLen, and_comm]
    · simp [h, Ne.symm h]
  calc
    _ = ∑ j ∈ range k, #{c ∈ μ.cells | c.2 = j} := by
      simp only [colLen_eq_card, col]
    _ = #{c ∈ μ.cells | c.2 < k} := by
      simpa only [mem_range] using
        sum_card_fiberwise_eq_card_filter μ.cells (range k) Prod.snd
    _ = ∑ i ∈ range (μ.colLen 0), #{c ∈ {c ∈ μ.cells | c.2 < k} | c.1 = i} :=
      card_eq_sum_card_fiberwise hf
    _ = _ := by simp only [hr, card_product, card_singleton, card_range, one_mul]

end YoungDiagram

namespace Nat.Partition

/-- Sum of the first `k` parts, with the parts in decreasing order and padded with zeros. -/
def partialSum {n : ℕ} (μ : Partition n) (k : ℕ) : ℕ :=
  ((μ.parts.sort (· ≥ ·)).take k).sum

@[simp]
theorem partialSum_zero {n : ℕ} (μ : Partition n) : μ.partialSum 0 = 0 := by
  simp [partialSum]

theorem partialSum_eq_sum_take {n : ℕ} (μ : Partition n) (k : ℕ) :
    μ.partialSum k = ((μ.parts.sort (· ≥ ·)).take k).sum := rfl

/-- Express partial sums using the padded numerical parts. -/
theorem partialSum_eq_sum_part {n : ℕ} (μ : Partition n) (k : ℕ) :
    μ.partialSum k = ∑ i ∈ range k, μ.toIntegerPartition.part i := by
  rw [← IntegerPartition.size_take]
  simp [IntegerPartition.take, partialSum]

theorem partialSum_eq_sum_rowLen {n : ℕ} (μ : Partition n) (k : ℕ) :
    μ.partialSum k = ∑ i ∈ range k, (YoungDiagram.ofPartition μ).rowLen i := by
  rw [partialSum_eq_sum_take]
  rw [← YoungDiagram.rowLens_ofPartition_eq_sort_parts]
  exact (YoungDiagram.sum_rowLen_eq_sum_take_rowLens _ _).symm

theorem partialSum_succ {n : ℕ} (μ : Partition n) (k : ℕ) :
    μ.partialSum (k + 1) = μ.partialSum k + (YoungDiagram.ofPartition μ).rowLen k := by
  simp only [partialSum_eq_sum_rowLen, Finset.sum_range_succ]

theorem partialSum_mono {n : ℕ} (μ : Partition n) : Monotone μ.partialSum := by
  intro i j hij
  rw [partialSum_eq_sum_rowLen, partialSum_eq_sum_rowLen]
  exact Finset.sum_le_sum_of_subset_of_nonneg (range_mono hij) (fun _ _ _ => Nat.zero_le _)

theorem partialSum_eq_of_card_le {n : ℕ} (μ : Partition n) {k : ℕ}
    (hk : μ.parts.card ≤ k) : μ.partialSum k = n := by
  rw [partialSum_eq_sum_take, List.take_of_length_le (by simpa using hk),
    ← Multiset.sum_coe, Multiset.sort_eq, μ.parts_sum]

theorem partialSum_le {n : ℕ} (μ : Partition n) (k : ℕ) : μ.partialSum k ≤ n := by
  calc
    μ.partialSum k ≤ μ.partialSum (max k μ.parts.card) := μ.partialSum_mono (le_max_left _ _)
    _ = n := μ.partialSum_eq_of_card_le (le_max_right _ _)

/-- Partial sums of the conjugate count the first `k` columns of the original partition. -/
theorem partialSum_conjugate {n : ℕ} (μ : Partition n) (k : ℕ) :
    μ.conjugate.partialSum k = (μ.parts.map (min k)).sum := by
  simp only [partialSum_eq_sum_rowLen, conjugate, YoungDiagram.ofPartition_toPartition,
    YoungDiagram.rowLen_transpose]
  rw [YoungDiagram.sum_colLen_eq_sum_min_rowLen]
  have h := congrArg (fun l : List ℕ => (l.map (min k)).sum)
    (YoungDiagram.rowLens_ofPartition_eq_sort_parts μ)
  simpa only [YoungDiagram.rowLens, List.map_map, Function.comp_def,
    Finset.sum_eq_multiset_sum, Finset.range_val, Multiset.range,
    ← Multiset.sum_coe, ← Multiset.map_coe, Multiset.sort_eq] using h

theorem partialSum_eq_sum_min_conjugate {n : ℕ} (μ : Partition n) (k : ℕ) :
    μ.partialSum k = (μ.conjugate.parts.map (min k)).sum := by
  simpa only [conjugate_conjugate] using partialSum_conjugate μ.conjugate k

/-- Conjugation as a permutation of the partitions of `n`. -/
def conjugateEquiv (n : ℕ) : Partition n ≃ Partition n where
  toFun := conjugate
  invFun := conjugate
  left_inv := conjugate_conjugate
  right_inv := conjugate_conjugate

@[simp]
theorem conjugateEquiv_apply {n : ℕ} (μ : Partition n) :
    conjugateEquiv n μ = μ.conjugate := rfl

@[simp]
theorem conjugateEquiv_symm_apply {n : ℕ} (μ : Partition n) :
    (conjugateEquiv n).symm μ = μ.conjugate := rfl

/-- A partition is determined by its partial sums. -/
theorem partialSum_injective (n : ℕ) : Function.Injective (partialSum (n := n)) := by
  intro μ ν h
  have hr (k : ℕ) :
      (YoungDiagram.ofPartition μ).rowLen k = (YoungDiagram.ofPartition ν).rowLen k := by
    have hs := congrFun h (k + 1)
    rw [partialSum_succ, partialSum_succ, congrFun h k] at hs
    exact Nat.add_left_cancel hs
  have hd : YoungDiagram.ofPartition μ = YoungDiagram.ofPartition ν := by
    ext ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, hr]
  apply Nat.Partition.ext
  have hp := congrArg (fun d : YoungDiagram => (d.rowLens : Multiset ℕ)) hd
  simpa only [YoungDiagram.rowLens_ofPartition_eq_sort_parts, Multiset.sort_eq] using hp

/-- `μ` dominates `ν` if every initial sum of parts of `ν` is at most that of `μ`. -/
def Dominates {n : ℕ} (μ ν : Partition n) : Prop := ∀ k, ν.partialSum k ≤ μ.partialSum k

@[refl]
theorem Dominates.refl {n : ℕ} (μ : Partition n) : μ.Dominates μ := fun _ => le_rfl

@[trans]
theorem Dominates.trans {n : ℕ} {μ ν π : Partition n}
    (hμν : μ.Dominates ν) (hνπ : ν.Dominates π) : μ.Dominates π :=
  fun k => (hνπ k).trans (hμν k)

theorem Dominates.antisymm {n : ℕ} {μ ν : Partition n}
    (hμν : μ.Dominates ν) (hνμ : ν.Dominates μ) : μ = ν :=
  partialSum_injective n (funext fun k => (hνμ k).antisymm (hμν k))

/-- Dominance only needs to be checked up to the number of parts of the dominating partition. -/
theorem dominates_iff_forall_le {n : ℕ} (μ ν : Partition n) :
    μ.Dominates ν ↔ ∀ k ≤ μ.parts.card, ν.partialSum k ≤ μ.partialSum k := by
  constructor
  · intro h k _
    exact h k
  · intro h k
    by_cases hk : k ≤ μ.parts.card
    · exact h k hk
    · rw [μ.partialSum_eq_of_card_le (Nat.le_of_not_ge hk)]
      exact ν.partialSum_le k

instance {n : ℕ} (μ ν : Partition n) : Decidable (μ.Dominates ν) :=
  decidable_of_iff (∀ k ≤ μ.parts.card, ν.partialSum k ≤ μ.partialSum k)
    (dominates_iff_forall_le μ ν).symm

/-- The dominance partial order: `μ ≤ ν` means `ν.Dominates μ`.
Enable this instance locally when order notation is useful. -/
@[instance_reducible]
def dominanceOrder (n : ℕ) : PartialOrder (Partition n) where
  le μ ν := ν.Dominates μ
  le_refl := Dominates.refl
  le_trans _ _ _ hμν hνπ := hνπ.trans hμν
  le_antisymm _ _ hμν hνμ := hνμ.antisymm hμν

end Nat.Partition
