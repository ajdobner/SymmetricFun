module

public import SymmetricFun.Matrix.WithMargins
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Card

/-!
# Binary matrices with prescribed margins

`Matrix.BinaryWithMargins r c` consists of natural-number matrices with margins
`r` and `c` whose entries are at most one. It specializes `Matrix.WithMargins`,
which supplies the shared margin identities and finiteness.

Reindexing rows and columns gives an equivalence of these types, so their cardinality
is independent of the chosen labels.

The sum over any set of columns is bounded by the sum of the corresponding
truncated row sums. When the column sums count initial segments of the rows,
there is exactly one matrix: the Ferrers matrix.
-/

@[expose] public section

namespace Matrix

open Finset

variable {I J I' J' : Type*} [Fintype I] [Fintype J]
  [Fintype I'] [Fintype J']

/-- Natural-number matrices with prescribed margins and entries at most one. -/
abbrev BinaryWithMargins (r : I → ℕ) (c : J → ℕ) :=
  {B : Matrix I J ℕ // B.HasMargins r c ∧ ∀ i j, B i j ≤ 1}

namespace BinaryWithMargins

variable {r : I → ℕ} {c : J → ℕ}

/-- Forget the bound of one on the entries. -/
def toWithMargins (B : BinaryWithMargins r c) : WithMargins r c :=
  ⟨B.val, B.property.1⟩

@[simp]
theorem toWithMargins_val (B : BinaryWithMargins r c) :
    B.toWithMargins.val = B.val := rfl

theorem toWithMargins_injective :
    Function.Injective (toWithMargins (r := r) (c := c)) :=
  fun _ _ h => Subtype.ext (congrArg (fun B : WithMargins r c => B.val) h)

instance : Finite (BinaryWithMargins r c) :=
  Finite.of_injective toWithMargins toWithMargins_injective

@[simp]
theorem row_sum (B : BinaryWithMargins r c) (i : I) :
    ∑ j, B.val i j = r i :=
  B.toWithMargins.row_sum i

@[simp]
theorem column_sum (B : BinaryWithMargins r c) (j : J) :
    ∑ i, B.val i j = c j :=
  B.toWithMargins.column_sum j

theorem entry_le_one (B : BinaryWithMargins r c) (i : I) (j : J) :
    B.val i j ≤ 1 :=
  B.property.2 i j

/-- A row contributes at most one per chosen column, and at most its entire row sum. -/
theorem row_sum_subset_le (B : BinaryWithMargins r c) (i : I) (s : Finset J) :
    ∑ j ∈ s, B.val i j ≤ min s.card (r i) := by
  apply le_min
  · calc
      ∑ j ∈ s, B.val i j ≤ ∑ j ∈ s, 1 := sum_le_sum fun j _ => B.entry_le_one i j
      _ = s.card := by simp
  · rw [← B.row_sum i]
    exact sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _

/-- The total in a set of columns is bounded by the truncated row sums. -/
theorem sum_columns_le (B : BinaryWithMargins r c) (s : Finset J) :
    ∑ j ∈ s, c j ≤ ∑ i, min s.card (r i) := by
  simp_rw [← B.column_sum]
  rw [sum_comm]
  exact sum_le_sum fun i _ => B.row_sum_subset_le i s

/-- Relabelling rows and columns preserves the corresponding margin constraints. -/
def reindex (e : I ≃ I') (f : J ≃ J') :
    BinaryWithMargins r c ≃ BinaryWithMargins (r ∘ e.symm) (c ∘ f.symm) where
  toFun B := ⟨Matrix.reindex e f B.val,
    B.property.1.reindex e f, fun i j => B.entry_le_one (e.symm i) (f.symm j)⟩
  invFun B := ⟨Matrix.reindex e.symm f.symm B.val, by
    refine ⟨?_, fun i j => B.entry_le_one (e i) (f j)⟩
    simpa only [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply] using
      B.property.1.reindex e.symm f.symm⟩
  left_inv B := by
    apply Subtype.ext
    ext i j
    simp
  right_inv B := by
    apply Subtype.ext
    ext i j
    simp

/-- The number of binary matrices is unchanged by independently relabelling the margins. -/
theorem card_reindex (e : I ≃ I') (f : J ≃ J') :
    Nat.card (BinaryWithMargins (r ∘ e.symm) (c ∘ f.symm)) =
      Nat.card (BinaryWithMargins r c) :=
  Nat.card_congr (reindex e f).symm

/-- The Ferrers matrix puts the ones in each row in an initial segment.
The row labels need not be ordered. -/
def ferrers {N : ℕ} (r : I → ℕ) (h : ∀ i, r i ≤ N) :
    BinaryWithMargins r (fun j : Fin N => ∑ i, if j.val < r i then 1 else 0) :=
  ⟨Matrix.of (fun i j => if j.val < r i then 1 else 0), by
    refine ⟨⟨?_, fun _ => rfl⟩, ?_⟩
    · intro i
      simpa only [Matrix.of_apply, sum_boole, ← Fintype.card_subtype, Nat.cast_id] using
        Fintype.card_fin_lt_of_le (h i)
    · intro i j
      simp only [Matrix.of_apply]
      split_ifs <;> simp⟩

/-- Ferrers margins force every entry. The first column fills every nonempty row;
removing it reduces all positive row sums by one. -/
theorem apply_eq_ite_of_ferrers_margins :
    ∀ (N : ℕ) (r : I → ℕ)
      (B : BinaryWithMargins r (fun j : Fin N => ∑ i, if j.val < r i then 1 else 0)),
      ∀ i j, B.val i j = if j.val < r i then 1 else 0 := by
  intro N
  induction N with
  | zero =>
      intro r B i j
      exact Fin.elim0 j
  | succ N ih =>
      intro r B
      have hle (i : I) : B.val i 0 ≤ if 0 < r i then 1 else 0 := by
        split_ifs with hi
        · exact B.entry_le_one i 0
        · exact (B.toWithMargins.entry_le_row i 0).trans
            (Nat.le_zero.mpr (Nat.eq_zero_of_not_pos hi))
      have hfirst (i : I) : B.val i 0 = if 0 < r i then 1 else 0 :=
        (sum_eq_sum_iff_of_le (fun i _ => hle i)).mp (B.column_sum 0) i (mem_univ i)
      let B' : BinaryWithMargins (fun i => r i - 1)
          (fun j : Fin N => ∑ i, if j.val < r i - 1 then 1 else 0) :=
        ⟨Matrix.of (fun i j => B.val i j.succ), by
          refine ⟨⟨?_, ?_⟩, fun i j => B.entry_le_one i j.succ⟩
          · intro i
            have h := B.row_sum i
            rw [Fin.sum_univ_succ, hfirst i] at h
            change ∑ j : Fin N, B.val i j.succ = r i - 1
            split_ifs at h <;> omega
          · intro j
            simpa only [Matrix.of_apply, Fin.val_succ, Nat.lt_sub_iff_add_lt] using
              B.column_sum j.succ⟩
      intro i j
      refine Fin.cases (hfirst i) (fun j => ?_) j
      simpa only [B', Matrix.of_apply, Fin.val_succ, Nat.lt_sub_iff_add_lt] using ih _ B' i j

/-- There is exactly one binary matrix with Ferrers margins. -/
theorem card_ferrers {N : ℕ} (r : I → ℕ) (h : ∀ i, r i ≤ N) :
    Nat.card (BinaryWithMargins r (fun j : Fin N => ∑ i, if j.val < r i then 1 else 0)) = 1 := by
  let : Unique (BinaryWithMargins r (fun j : Fin N => ∑ i, if j.val < r i then 1 else 0)) :=
    ⟨⟨ferrers r h⟩, fun B => by
      apply Subtype.ext
      ext i j
      exact apply_eq_ite_of_ferrers_margins N r B i j⟩
  exact Nat.card_unique

end BinaryWithMargins

end Matrix
