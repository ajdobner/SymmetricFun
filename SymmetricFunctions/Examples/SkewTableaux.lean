import SymmetricFunctions.Tableaux.Skew
import Mathlib.Data.ZMod.Basic

/-! # Missing cells, empty shapes, and genuine noncontainment -/
noncomputable section
namespace SymmetricFunctions.Partition.Examples
open SkewTableau

example (ξ : Nat.Partition 7) : Fintype.card (SkewTableau ξ ξ 0) = 1 := by simp
example (ξ : Nat.Partition 7) : generatingPolynomial ξ ξ 0 (ZMod 6) = 1 := by simp
example (ξ : Nat.Partition 7) (μ : Nat.Partition 0) :
    generatingPolynomial ξ μ 3 ℤ = FiniteTableau.generatingPolynomial ξ 3 ℤ := by simp

private def shape21 : Nat.Partition 3 := Nat.Partition.ofSums 3 {2, 1} (by decide)

private theorem rows_shape21 (i : ℕ) :
    rowLength shape21 i = if i = 0 then 2 else if i = 1 then 1 else 0 := by
  have hs : shape21.parts.sort (· ≥ ·) = [2, 1] := by
    norm_num [shape21, Nat.Partition.ofSums, Multiset.sort_cons, Multiset.filter_singleton]
  rcases i with _ | i
  · simpa [hs] using rowLength_eq_getElem_sort shape21 0 (by decide)
  rcases i with _ | i
  · simpa [hs] using rowLength_eq_getElem_sort shape21 1 (by decide)
  · rw [rowLength_eq_zero _ (by change 2 ≤ i + 1 + 1; omega)]
    simp

private theorem hole_strip : HorizontalStrip (Nat.Partition.indiscrete 1) shape21 := by
  constructor
  · apply (contained_iff_rowLength _ _).mpr
    intro i
    simp only [rowLength_indiscrete, rows_shape21]
    split_ifs <;> omega
  · intro i
    cases i <;> simp [rows_shape21, rowLength_indiscrete]

-- The cells (0,1) and (1,0) may both contain 0. The hole (0,0) is not compared.
private def holeTableau : SkewTableau shape21 (Nat.Partition.indiscrete 1) 1 :=
  constant hole_strip 0

example (c : SkewCell shape21 (Nat.Partition.indiscrete 1)) : holeTableau.entry c = 0 := rfl
example : holeTableau.content = Finsupp.single 0 2 := content_one _
example : generatingPolynomial shape21 (Nat.Partition.indiscrete 1) 1 (ZMod 6) =
    MvPolynomial.X (0 : Fin 1) ^ 2 := generatingPolynomial_one_of_horizontalStrip _ hole_strip

private theorem not_contained : ¬ Contained (Nat.Partition.indiscrete 2).conjugate
    (Nat.Partition.indiscrete 3) := by
  intro h
  have hh := (contained_iff_rowLength _ _).mp h 1
  simp at hh

-- Its raw cell difference is nonempty, but a noncontained pair has no skew tableaux.
example : IsEmpty (SkewTableau (Nat.Partition.indiscrete 3)
    (Nat.Partition.indiscrete 2).conjugate 4) := isEmpty_of_not_contained not_contained
example : generatingPolynomial (Nat.Partition.indiscrete 3)
    (Nat.Partition.indiscrete 2).conjugate 4 ℤ = 0 :=
  generatingPolynomial_eq_zero_of_not_contained _ not_contained

end SymmetricFunctions.Partition.Examples
