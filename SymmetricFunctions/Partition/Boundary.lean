import SymmetricFunctions.Partition.YoungDiagram
import Mathlib.Data.Fintype.EquivFin

/-!
# Complementary addresses along a Young diagram boundary

The row and column addresses partition a finite interval. Columns are those of
Mathlib's Young diagram, with the second block listed in reverse column order.
These addresses do not redefine partition conjugation.
-/

namespace SymmetricFunctions.Partition

variable {d : ℕ}

/-- Width of the Young diagram, zero for the empty shape. -/
def width (ξ : Nat.Partition d) : ℕ := rowLength ξ 0

@[simp] theorem length_conjugate_eq_width (ξ : Nat.Partition d) :
    length ξ.conjugate = width ξ := length_conjugate ξ

theorem rowLength_le_width (ξ : Nat.Partition d) (i : ℕ) : rowLength ξ i ≤ width ξ :=
  rowLength_antitone ξ (Nat.zero_le i)

/-- Addresses of the rows selected from the complete Toeplitz matrix. -/
def boundaryRow (ξ : Nat.Partition d) (i : Fin (length ξ)) : Fin (length ξ + width ξ) :=
  ⟨width ξ - rowLength ξ i + i.val, by have := i.isLt; omega⟩

/-- The complementary addresses, from columns in reverse order. -/
def boundaryColumn (ξ : Nat.Partition d) (j : Fin (width ξ)) : Fin (length ξ + width ξ) :=
  ⟨j.val + (YoungDiagram.ofPartition ξ).colLen (width ξ - 1 - j.val), by
    have hc := YoungDiagram.colLen_anti (YoungDiagram.ofPartition ξ) 0
      (width ξ - 1 - j.val) (Nat.zero_le _)
    rw [colLen_zero] at hc
    have := j.isLt
    omega⟩

/-- The selected addresses retain the decreasing-row ordering of the determinant. -/
theorem boundaryRow_strictMono (ξ : Nat.Partition d) : StrictMono (boundaryRow ξ) := by
  intro i j hij
  have hr := rowLength_antitone ξ (show i.val ≤ j.val by omega)
  have hi := rowLength_le_width ξ i
  have hj := rowLength_le_width ξ j
  change width ξ - rowLength ξ i + i.val < width ξ - rowLength ξ j + j.val
  omega

/-- Reversing columns makes the complementary addresses increasing. -/
theorem boundaryColumn_strictMono (ξ : Nat.Partition d) : StrictMono (boundaryColumn ξ) := by
  intro i j hij
  have hc := YoungDiagram.colLen_anti (YoungDiagram.ofPartition ξ)
    (width ξ - 1 - j.val) (width ξ - 1 - i.val) (by omega)
  change i.val + (YoungDiagram.ofPartition ξ).colLen (width ξ - 1 - i.val) <
    j.val + (YoungDiagram.ofPartition ξ).colLen (width ξ - 1 - j.val)
  omega

/-- A cell cannot simultaneously lie on both sides of its diagram boundary. -/
theorem boundaryRow_ne_boundaryColumn (ξ : Nat.Partition d)
    (i : Fin (length ξ)) (j : Fin (width ξ)) : boundaryRow ξ i ≠ boundaryColumn ξ j := by
  intro he
  have he := congrArg Fin.val he
  change width ξ - rowLength ξ i + i.val =
    j.val + (YoungDiagram.ofPartition ξ).colLen (width ξ - 1 - j.val) at he
  have hcell : width ξ - 1 - j.val < rowLength ξ i ↔
      i.val < (YoungDiagram.ofPartition ξ).colLen (width ξ - 1 - j.val) :=
    YoungDiagram.mem_iff_lt_rowLen.symm.trans YoungDiagram.mem_iff_lt_colLen
  have hr := rowLength_le_width ξ i
  have hj := j.isLt
  omega

/-- Cross-boundary order records whether the corresponding cell belongs to the shape. -/
theorem boundaryRow_lt_boundaryColumn_iff (ξ : Nat.Partition d)
    (i : Fin (length ξ)) (j : Fin (width ξ)) :
    boundaryRow ξ i < boundaryColumn ξ j ↔ width ξ - 1 - j.val < rowLength ξ i := by
  have hcell : width ξ - 1 - j.val < rowLength ξ i ↔
      i.val < (YoungDiagram.ofPartition ξ).colLen (width ξ - 1 - j.val) :=
    YoungDiagram.mem_iff_lt_rowLen.symm.trans YoungDiagram.mem_iff_lt_colLen
  have hr := rowLength_le_width ξ i
  have hj := j.isLt
  change width ξ - rowLength ξ i + i.val <
    j.val + (YoungDiagram.ofPartition ξ).colLen (width ξ - 1 - j.val) ↔ _
  omega

/-- The two boundary lists enumerate the entire finite interval without repetition. -/
noncomputable def boundaryEquiv (ξ : Nat.Partition d) :
    Fin (length ξ) ⊕ Fin (width ξ) ≃ Fin (length ξ + width ξ) :=
  Equiv.ofBijective (Sum.elim (boundaryRow ξ) (boundaryColumn ξ))
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro a b hab
      cases a with
      | inl i =>
        cases b with
        | inl j => exact congrArg Sum.inl ((boundaryRow_strictMono ξ).injective hab)
        | inr j => exact False.elim (boundaryRow_ne_boundaryColumn ξ i j hab)
      | inr i =>
        cases b with
        | inl j => exact False.elim (boundaryRow_ne_boundaryColumn ξ j i hab.symm)
        | inr j => exact congrArg Sum.inr ((boundaryColumn_strictMono ξ).injective hab),
      by simp⟩)

@[simp] theorem boundaryEquiv_inl (ξ : Nat.Partition d) (i : Fin (length ξ)) :
    boundaryEquiv ξ (Sum.inl i) = boundaryRow ξ i := rfl

@[simp] theorem boundaryEquiv_inr (ξ : Nat.Partition d) (j : Fin (width ξ)) :
    boundaryEquiv ξ (Sum.inr j) = boundaryColumn ξ j := rfl

end SymmetricFunctions.Partition
