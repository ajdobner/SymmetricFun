import SymmetricFunctions.Partition.YoungDiagram

/-! Row padding and shape conventions, without a competing partition type. -/
namespace SymmetricFunctions.Examples

open SymmetricFunctions.Partition

private def partition21 : Nat.Partition 3 := Nat.Partition.ofSums 3 {2, 1} (by decide)

private theorem sorted_partition21 : partition21.parts.sort (· ≥ ·) = [2, 1] := by
  norm_num [partition21, Nat.Partition.ofSums, Multiset.sort_cons, Multiset.filter_singleton]

example : length partition21 = 2 := by decide
example : rowLength partition21 0 = 2 := by
  simpa only [sorted_partition21, List.getElem_cons_zero] using
    rowLength_eq_getElem_sort partition21 0 (by decide)
example : rowLength partition21 1 = 1 := by
  simpa only [sorted_partition21, List.getElem_cons_succ, List.getElem_cons_zero] using
    rowLength_eq_getElem_sort partition21 1 (by decide)
example : rowLength partition21 2 = 0 := rowLength_eq_zero _ (by decide)
example : ∑ i ∈ Finset.range 7, rowLength partition21 i = 3 :=
  sum_rowLength_padded _ (by decide)
example (i : ℕ) : rowLength (Nat.Partition.indiscrete 0) i = 0 := by simp
example : rowLength (Nat.Partition.indiscrete 3).conjugate 2 = 1 := by simp
example : rowLength (Nat.Partition.indiscrete 3).conjugate 3 = 0 := by simp
example (ξ : Nat.Partition 3) : Contained ξ.conjugate.conjugate ξ := by simp

end SymmetricFunctions.Examples
