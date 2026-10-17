module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Natural-number matrices with prescribed margins

`Matrix.HasMargins B r c` specifies the row and column sums of `B`.
`Matrix.WithMargins r c` bundles natural-number matrices satisfying these constraints.

Each entry is bounded by both its row sum and its column sum, so the type is finite.
Reindexing rows and columns gives an equivalence, and therefore preserves the count.
The index types are arbitrary finite types, with no ordering assumptions.
-/

@[expose] public section

namespace Matrix

variable {I J I' J' : Type*} [Fintype I] [Fintype J]
  [Fintype I'] [Fintype J']

/-- A matrix has margins `r` and `c` when these are its row and column sums. -/
def HasMargins (B : Matrix I J ℕ) (r : I → ℕ) (c : J → ℕ) : Prop :=
  (∀ i, ∑ j, B i j = r i) ∧ (∀ j, ∑ i, B i j = c j)

instance (B : Matrix I J ℕ) (r : I → ℕ) (c : J → ℕ) :
    Decidable (B.HasMargins r c) :=
  inferInstanceAs (Decidable
    ((∀ i, ∑ j, B i j = r i) ∧ (∀ j, ∑ i, B i j = c j)))

namespace HasMargins

variable {B : Matrix I J ℕ} {r : I → ℕ} {c : J → ℕ}

theorem row_sum (h : B.HasMargins r c) (i : I) : ∑ j, B i j = r i :=
  h.1 i

theorem column_sum (h : B.HasMargins r c) (j : J) : ∑ i, B i j = c j :=
  h.2 j

theorem entry_le_row (h : B.HasMargins r c) (i : I) (j : J) : B i j ≤ r i := by
  rw [← h.row_sum i]
  exact Finset.single_le_sum (fun k _ => Nat.zero_le (B i k)) (Finset.mem_univ j)

theorem entry_le_column (h : B.HasMargins r c) (i : I) (j : J) : B i j ≤ c j := by
  rw [← h.column_sum j]
  exact Finset.single_le_sum (fun k _ => Nat.zero_le (B k j)) (Finset.mem_univ i)

/-- Reindexing a matrix relabels its margins by the same equivalences. -/
theorem reindex (h : B.HasMargins r c) (e : I ≃ I') (f : J ≃ J') :
    (Matrix.reindex e f B).HasMargins (r ∘ e.symm) (c ∘ f.symm) := by
  constructor
  · intro i
    exact (f.symm.sum_comp fun j => B (e.symm i) j).trans (h.row_sum _)
  · intro j
    exact (e.symm.sum_comp fun i => B i (f.symm j)).trans (h.column_sum _)

end HasMargins

/-- Natural-number matrices with specified row and column sums. -/
abbrev WithMargins (r : I → ℕ) (c : J → ℕ) :=
  {B : Matrix I J ℕ // B.HasMargins r c}

namespace WithMargins

variable {r : I → ℕ} {c : J → ℕ}

@[simp]
theorem row_sum (B : WithMargins r c) (i : I) :
    ∑ j, B.val i j = r i :=
  B.property.row_sum i

@[simp]
theorem column_sum (B : WithMargins r c) (j : J) :
    ∑ i, B.val i j = c j :=
  B.property.column_sum j

theorem entry_le_row (B : WithMargins r c) (i : I) (j : J) : B.val i j ≤ r i :=
  B.property.entry_le_row i j

theorem entry_le_column (B : WithMargins r c) (i : I) (j : J) : B.val i j ≤ c j :=
  B.property.entry_le_column i j

/-- The row bounds embed matrices with fixed margins into a finite family of finite types. -/
instance : Finite (WithMargins r c) := by
  let f : WithMargins r c → ∀ i : I, J → Fin (r i + 1) :=
    fun B i j => ⟨B.val i j, Nat.lt_succ_of_le (B.entry_le_row i j)⟩
  apply Finite.of_injective f
  intro B C h
  apply Subtype.ext
  ext i j
  exact congrArg Fin.val (congrFun (congrFun h i) j)

/-- Relabelling rows and columns gives an equivalence of matrices with prescribed margins. -/
def reindex (e : I ≃ I') (f : J ≃ J') :
    WithMargins r c ≃ WithMargins (r ∘ e.symm) (c ∘ f.symm) where
  toFun B := ⟨Matrix.reindex e f B.val, B.property.reindex e f⟩
  invFun B := ⟨Matrix.reindex e.symm f.symm B.val, by
    simpa only [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply] using
      B.property.reindex e.symm f.symm⟩
  left_inv B := by
    apply Subtype.ext
    ext i j
    simp
  right_inv B := by
    apply Subtype.ext
    ext i j
    simp

/-- The number of matrices is unchanged by independently relabelling their margins. -/
theorem card_reindex (e : I ≃ I') (f : J ≃ J') :
    Nat.card (WithMargins (r ∘ e.symm) (c ∘ f.symm)) =
      Nat.card (WithMargins r c) :=
  Nat.card_congr (reindex e f).symm

end WithMargins

end Matrix
