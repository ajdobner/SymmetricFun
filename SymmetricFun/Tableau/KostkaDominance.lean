module

public import SymmetricFun.Tableau.Kostka
public import SymmetricFun.Partition.Dominance

/-!
# Dominance and the diagonal of the Kostka matrix

An ordinary tableau has at most `r` parts after its first `r` steps. The size of
that intermediate partition is therefore bounded by the first `r` parts of the
final shape. For partition weights, this proves that the shape dominates the weight.

When shape and weight agree, every intermediate partition is forced to be the
corresponding prefix of the shape. Thus `kostka π π = 1`. Together with vanishing
outside dominance, this makes the Kostka matrix unitriangular.
-/

@[expose] public section

open IntegerPartition SkewSemistandardYoungTableau

namespace SkewSemistandardYoungTableau.WithWeight

/-- The shape of an ordinary tableau dominates its partition weight.
The alphabet may include trailing zero entries. -/
theorem dominates {n k : ℕ} {π μ : Nat.Partition n}
    (c : WithWeight empty π.toIntegerPartition (fun i : Fin k => μ.toIntegerPartition.part i))
    (hk : μ.parts.card ≤ k) : π.Dominates μ := by
  have hsize (i : Fin (k + 1)) : (c.val i).size = μ.partialSum i := by
    rw [c.size_eq_prefix_sum, Nat.Partition.partialSum_eq_sum_part]
    simp only [size_empty, zero_add, Fin.val_castLE]
    rw [Fin.sum_univ_eq_sum_range]
  have hprefix (i : Fin (k + 1)) : μ.partialSum i ≤ π.partialSum i := by
    rw [← hsize, Nat.Partition.partialSum_eq_sum_part, ← size_take]
    exact size_le_size_of_part_le (c.part_le_take i)
  intro r
  by_cases hr : r ≤ k
  · exact hprefix ⟨r, Nat.lt_succ_of_le hr⟩
  · calc
      μ.partialSum r ≤ n := μ.partialSum_le r
      _ = μ.partialSum k := (μ.partialSum_eq_of_card_le hk).symm
      _ ≤ π.partialSum k := hprefix (Fin.last k)
      _ ≤ π.partialSum r := π.partialSum_mono (by omega)

end SkewSemistandardYoungTableau.WithWeight

namespace Nat.Partition

variable {n : ℕ}

private theorem get_sort_parts_eq_part (μ : Partition n) :
    (μ.parts.sort (· ≥ ·)).get =
      fun i : Fin (μ.parts.sort (· ≥ ·)).length => μ.toIntegerPartition.part i := by
  funext i
  exact (List.getD_eq_getElem (μ.parts.sort (· ≥ ·)) 0 i.isLt).symm

/-- A nonzero Kostka number requires the shape to dominate the weight. -/
theorem dominates_of_kostka_ne_zero (π μ : Partition n) (h : kostka π μ ≠ 0) :
    π.Dominates μ := by
  unfold kostka skewKostka skewKostkaWeight at h
  rw [toIntegerPartition_zero, get_sort_parts_eq_part] at h
  obtain ⟨c⟩ := (Nat.card_ne_zero.mp h).1
  exact c.dominates (by simp)

theorem kostka_eq_zero_of_not_dominates (π μ : Partition n) (h : ¬ π.Dominates μ) :
    kostka π μ = 0 :=
  not_not.mp (fun hn => h (dominates_of_kostka_ne_zero π μ hn))

/-- The unique tableau of shape and weight `π` adds one whole part at each step. -/
@[simp]
theorem kostka_self (π : Partition n) : kostka π π = 1 := by
  unfold kostka skewKostka skewKostkaWeight
  rw [toIntegerPartition_zero, get_sort_parts_eq_part]
  exact Nat.card_of_subsingleton (WithWeight.rowTableau π.toIntegerPartition (by simp))

end Nat.Partition
