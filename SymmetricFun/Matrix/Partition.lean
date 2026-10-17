module

public import SymmetricFun.Matrix.Binary
public import SymmetricFun.Partition.Dominance
public import Mathlib.Data.Fintype.Fin

/-!
# Binary matrices with partition margins

`Matrix.BinaryWithPartitionMargins α β` uses the decreasing parts of `α` and `β`
as row and column sums. This is a particular labelling of `Matrix.BinaryWithMargins`.

The existence of such a matrix implies that `α.conjugate` dominates `β`.
When `β = α.conjugate`, there is exactly one matrix, given by the cells of the
Young diagram of `α`.
-/

@[expose] public section

open Finset

namespace YoungDiagram

/-- Enumerating the nonempty rows gives the multiset of row lengths. -/
theorem map_rowLen (μ : YoungDiagram) :
    (univ : Finset (Fin (μ.colLen 0))).val.map (fun i : Fin (μ.colLen 0) => μ.rowLen i) =
      (μ.rowLens : Multiset ℕ) := by
  rw [Fin.univ_val_map, List.ofFn_eq_map]
  change (((List.finRange (μ.colLen 0)).map (μ.rowLen ∘ Fin.val)) : Multiset ℕ) = _
  rw [← List.map_map, List.map_coe_finRange_eq_range]
  rfl

/-- A prefix sum can be taken over the finite set of nonempty rows. -/
theorem sum_rowLen_filter_lt (μ : YoungDiagram) (k : ℕ) :
    ∑ i : Fin (μ.colLen 0) with i.val < k, μ.rowLen i =
      ∑ i ∈ range k, μ.rowLen i := by
  rw [sum_filter, Fin.sum_univ_eq_sum_range (fun i => if i < k then μ.rowLen i else 0),
    ← sum_filter]
  have hs : (range (μ.colLen 0)).filter (fun i => i < k) = range (min (μ.colLen 0) k) := by
    ext i
    simp [lt_min_iff]
  rw [hs, μ.sum_rowLen_eq_sum_take_rowLens k]
  simp only [rowLens, ← List.map_take, List.take_range, Finset.sum_eq_multiset_sum,
    Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe, min_comm]

/-- Column lengths count rows containing the corresponding cell. -/
theorem sum_ite_lt_rowLen (μ : YoungDiagram) (j : ℕ) :
    ∑ i : Fin (μ.colLen 0), (if j < μ.rowLen i then 1 else 0 : ℕ) = μ.colLen j := by
  simp only [← mem_iff_lt_rowLen, mem_iff_lt_colLen, sum_boole, Nat.cast_id]
  rw [Fin.card_filter_val_lt, min_eq_right (μ.colLen_anti 0 j (Nat.zero_le _))]

/-- The cells of a Young diagram give the unique binary matrix with its row and column lengths. -/
theorem card_binaryWithMargins (μ : YoungDiagram) :
    Nat.card (Matrix.BinaryWithMargins
      (fun i : Fin (μ.colLen 0) => μ.rowLen i)
      (fun j : Fin (μ.rowLen 0) => μ.colLen j)) = 1 := by
  have hc : (fun j : Fin (μ.rowLen 0) => μ.colLen j) =
      fun j => ∑ i : Fin (μ.colLen 0), if j.val < μ.rowLen i then 1 else 0 :=
    funext fun j => (μ.sum_ite_lt_rowLen j).symm
  rw [hc]
  exact Matrix.BinaryWithMargins.card_ferrers _ (fun i => μ.rowLen_anti 0 i (Nat.zero_le _))

end YoungDiagram

namespace Nat.Partition

/-- The nonempty row lengths enumerate the parts in decreasing order. -/
theorem map_rowLen {n : ℕ} (μ : Partition n) :
    (univ : Finset (Fin ((YoungDiagram.ofPartition μ).colLen 0))).val.map
      (fun i : Fin ((YoungDiagram.ofPartition μ).colLen 0) =>
        (YoungDiagram.ofPartition μ).rowLen i) = μ.parts := by
  rw [YoungDiagram.map_rowLen, YoungDiagram.rowLens_ofPartition_eq_sort_parts,
    Multiset.sort_eq]

/-- The partial sum of a partition as a sum over its finite set of nonempty rows. -/
theorem partialSum_eq_sum_filter_rowLen {n : ℕ} (μ : Partition n) (k : ℕ) :
    μ.partialSum k = ∑ i : Fin ((YoungDiagram.ofPartition μ).colLen 0) with i.val < k,
      (YoungDiagram.ofPartition μ).rowLen i := by
  rw [partialSum_eq_sum_rowLen, YoungDiagram.sum_rowLen_filter_lt]

end Nat.Partition

namespace Matrix

/-- Binary matrices whose rows and columns are labelled by the decreasing parts
of two partitions. -/
abbrev BinaryWithPartitionMargins {n m : ℕ} (α : Nat.Partition n) (β : Nat.Partition m) :=
  BinaryWithMargins
    (fun i : Fin ((YoungDiagram.ofPartition α).colLen 0) =>
      (YoungDiagram.ofPartition α).rowLen i)
    (fun j : Fin ((YoungDiagram.ofPartition β).colLen 0) =>
      (YoungDiagram.ofPartition β).rowLen j)

namespace BinaryWithPartitionMargins

/-- Binary margins satisfy the dominance inequality. -/
theorem conjugate_dominates {n : ℕ} {α β : Nat.Partition n}
    (B : BinaryWithPartitionMargins α β) : α.conjugate.Dominates β := by
  intro k
  let s : Finset (Fin ((YoungDiagram.ofPartition β).colLen 0)) :=
    univ.filter fun i => i.val < k
  calc
    β.partialSum k = ∑ j ∈ s, (YoungDiagram.ofPartition β).rowLen j :=
      β.partialSum_eq_sum_filter_rowLen k
    _ ≤ ∑ i : Fin ((YoungDiagram.ofPartition α).colLen 0),
        min s.card ((YoungDiagram.ofPartition α).rowLen i) := B.sum_columns_le s
    _ ≤ ∑ i : Fin ((YoungDiagram.ofPartition α).colLen 0),
        min k ((YoungDiagram.ofPartition α).rowLen i) := by
      apply sum_le_sum
      intro i _
      apply min_le_min_right
      dsimp [s]
      rw [Fin.card_filter_val_lt]
      exact min_le_right _ _
    _ = α.conjugate.partialSum k := by
      rw [Nat.Partition.partialSum_conjugate, ← α.map_rowLen]
      simp only [Multiset.map_map, Function.comp_def, Finset.sum_map_val]

/-- Conjugate partition margins determine a unique binary matrix. -/
theorem card_conjugate {n : ℕ} (α : Nat.Partition n) :
    Nat.card (BinaryWithPartitionMargins α α.conjugate) = 1 := by
  unfold BinaryWithPartitionMargins
  rw [Nat.Partition.conjugate, YoungDiagram.ofPartition_toPartition,
    YoungDiagram.colLen_transpose]
  simpa only [YoungDiagram.rowLen_transpose] using
    (YoungDiagram.ofPartition α).card_binaryWithMargins

end BinaryWithPartitionMargins

end Matrix
