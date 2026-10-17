import SymmetricFunctions.Schur.Column
import Mathlib.Data.ZMod.Basic

/-! # Determinant conventions over arbitrary rings -/
namespace SymmetricFunction.Examples

noncomputable section
open SymmetricFunctions.Partition
variable {R : Type*} [CommRing R]

attribute [local irreducible] SymmetricFunction

-- Integer subtraction detects a negative index instead of producing h_0.
example : completeInt (R := R) ((0 : ℤ) - 1 + 0) = 0 := by simp
example : completeInt (R := R) ((1 : ℤ) - 1 + 0) = 1 := by simp
example (ξ : Nat.Partition 0) : schur (R := R) ξ = 1 := by simp
example (ξ : Nat.Partition 0) : (jacobiTrudiMatrix (R := R) ξ 5).det = 1 := by
  rw [det_jacobiTrudiMatrix _ (by simp), schur_zero]

private def shape21 : Nat.Partition 3 := Nat.Partition.ofSums 3 {2, 1} (by decide)

private theorem sorted_shape21 : shape21.parts.sort (· ≥ ·) = [2, 1] := by
  norm_num [shape21, Nat.Partition.ofSums, Multiset.sort_cons, Multiset.filter_singleton]

private theorem row0_shape21 : rowLength shape21 0 = 2 := by
  simpa only [sorted_shape21, List.getElem_cons_zero] using
    rowLength_eq_getElem_sort shape21 0 (by decide)

private theorem row1_shape21 : rowLength shape21 1 = 1 := by
  simpa only [sorted_shape21, List.getElem_cons_succ, List.getElem_cons_zero] using
    rowLength_eq_getElem_sort shape21 1 (by decide)

example : schur (R := R) shape21 = h 2 * h 1 - h 3 := by
  rw [← det_jacobiTrudiMatrix shape21 (L := 2) (by decide), Matrix.det_fin_two]
  norm_num [jacobiTrudiMatrix, row0_shape21, row1_shape21, completeInt]

example : (jacobiTrudiMatrix (R := R) shape21 7).det = schur shape21 :=
  det_jacobiTrudiMatrix _ (by decide)

example : IsHomogeneous (schur (R := ZMod 6) shape21) 3 := isHomogeneous_schur _
example : schur (R := PUnit) shape21 = 0 := by
  apply (polynomialEquiv PUnit).injective
  exact Subsingleton.elim _ _
example (n : ℕ) : schur (R := R) (Nat.Partition.indiscrete n).conjugate = e n := by simp
example : rho R 1 (schur (Nat.Partition.indiscrete 2).conjugate) = 0 := by
  rw [schur_indiscrete_conjugate, rho_e_eq_zero R (by decide)]

end
end SymmetricFunction.Examples
