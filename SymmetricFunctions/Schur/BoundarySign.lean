import SymmetricFunctions.Partition.Boundary
import SymmetricFunctions.Schur.ShuffleSign
import Mathlib.Order.Interval.Finset.Fin

/-! # The sign of the Young diagram boundary reindexing -/

namespace SymmetricFunctions.Partition

noncomputable section
open scoped BigOperators

variable {d : ℕ}

/-- Columns for Jacobi–Trudi occupy the final block of the finite interval. -/
def tailEquiv (l w : ℕ) : Fin l ⊕ Fin w ≃ Fin (l + w) :=
  ((Equiv.sumComm _ _).trans finSumFinEquiv).trans (finCongr (Nat.add_comm w l))

@[simp] theorem tailEquiv_inl_val {l w : ℕ} (i : Fin l) :
    (tailEquiv l w (Sum.inl i)).val = w + i.val := rfl

@[simp] theorem tailEquiv_inr_val {l w : ℕ} (j : Fin w) :
    (tailEquiv l w (Sum.inr j)).val = j.val := rfl

theorem sign_tailEquiv (l w : ℕ) :
    Equiv.Perm.sign (finSumFinEquiv.symm.trans (tailEquiv l w)) = (-1 : ℤˣ) ^ (l * w) := by
  rw [sign_orderedShuffle]
  · have hn (i : Fin l) (j : Fin w) : ¬ tailEquiv l w (Sum.inl i) <
        tailEquiv l w (Sum.inr j) := by
      change ¬ w + i.val < j.val
      have := j.isLt
      omega
    simp only [hn, ite_false, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← pow_mul, Nat.mul_comm]
  · intro i j hij
    change w + i.val < w + j.val
    omega
  · intro i j hij
    exact hij

private theorem prod_row_sign {w r : ℕ} (hr : r ≤ w) :
    (∏ j : Fin w, (if w - 1 - j.val < r then 1 else -1 : ℤˣ)) = (-1 : ℤˣ) ^ (w - r) := by
  have he : (∏ j : Fin w, (if w - 1 - j.val < r then 1 else -1 : ℤˣ)) =
      ∏ j : Fin w, (if j.val < r then 1 else -1 : ℤˣ) := by
    convert Equiv.prod_comp Fin.revPerm
      (fun j : Fin w => (if j.val < r then 1 else -1 : ℤˣ)) using 1
    apply Finset.prod_congr rfl
    intro j _
    congr 1
    simp only [Fin.revPerm_apply, Fin.val_rev]
    apply propext
    omega
  rw [he]
  rcases lt_or_eq_of_le hr with hlt | rfl
  · let k : Fin w := ⟨r, hlt⟩
    have hh : (∏ j : Fin w, (if j.val < r then 1 else -1 : ℤˣ)) =
        ∏ j : Fin w, (if j ∈ Finset.Ici k then -1 else 1 : ℤˣ) := by
      apply Finset.prod_congr rfl
      intro j _
      simp only [Finset.mem_Ici, Fin.le_def]
      change (if j.val < r then 1 else -1 : ℤˣ) = if r ≤ j.val then -1 else 1
      by_cases hj : j.val < r
      · simp only [hj, ite_true, Nat.not_le_of_gt hj, ite_false]
      · simp only [hj, ite_false, Nat.le_of_not_gt hj, ite_true]
    rw [hh, Finset.prod_ite_mem_eq]
    simp [Fin.card_Ici, k]
  · simp

/-- Boundary signs relative to a tail block count the cells of the partition. -/
theorem sign_boundary_mul_rectangle (ξ : Nat.Partition d) :
    Equiv.Perm.sign (finSumFinEquiv.symm.trans (boundaryEquiv ξ)) *
      (-1 : ℤˣ) ^ (length ξ * width ξ) = (-1 : ℤˣ) ^ d := by
  rw [sign_orderedShuffle _ (boundaryRow_strictMono ξ) (boundaryColumn_strictMono ξ)]
  simp only [boundaryEquiv_inl, boundaryEquiv_inr, boundaryRow_lt_boundaryColumn_iff]
  simp_rw [prod_row_sign (rowLength_le_width ξ _)]
  have hp : (-1 : ℤˣ) ^ (length ξ * width ξ) =
      ∏ _i : Fin (length ξ), (-1 : ℤˣ) ^ width ξ := by
    simp [← pow_mul, Nat.mul_comm]
  rw [hp, ← Finset.prod_mul_distrib]
  have hrow (i : Fin (length ξ)) : (-1 : ℤˣ) ^ (width ξ - rowLength ξ i) *
      (-1) ^ width ξ = (-1) ^ rowLength ξ i := by
    have hw := Nat.sub_add_cancel (rowLength_le_width ξ i)
    nth_rw 2 [← hw]
    rw [pow_add]
    simp [← mul_assoc, ← mul_pow]
  simp_rw [hrow]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (rowLength ξ) (length ξ)).trans (sum_rowLength ξ)

/-- The complement addresses differ from the initial interval by the partition size. -/
theorem sum_boundaryColumn (ξ : Nat.Partition d) :
    ∑ j : Fin (width ξ), (boundaryColumn ξ j).val =
      (∑ j : Fin (width ξ), j.val) + d := by
  simp only [boundaryColumn, Finset.sum_add_distrib]
  congr 1
  have hr : ∑ j : Fin (width ξ), rowLength ξ.conjugate j = d :=
    (Fin.sum_univ_eq_sum_range (rowLength ξ.conjugate) (width ξ)).trans
      (sum_rowLength_padded ξ.conjugate (by simp [width]))
  calc
    _ = ∑ j : Fin (width ξ), rowLength ξ.conjugate (Fin.revPerm j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [rowLength_conjugate]
      congr 1
      simp only [Fin.revPerm_apply, Fin.val_rev, Nat.sub_sub, Nat.add_comm]
    _ = _ := (Equiv.sum_comp Fin.revPerm _).trans hr

/-- The row/column reindexing contributes precisely the partition-size sign. -/
theorem sign_boundary_relative_tail (ξ : Nat.Partition d) :
    Equiv.Perm.sign ((boundaryEquiv ξ).trans (tailEquiv (length ξ) (width ξ)).symm) =
      (-1 : ℤˣ) ^ d := by
  rw [sign_relativeShuffle, sign_tailEquiv, sign_boundary_mul_rectangle]

end
end SymmetricFunctions.Partition
