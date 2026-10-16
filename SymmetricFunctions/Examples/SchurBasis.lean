import SymmetricFunctions.Basis.Schur
import Mathlib.Data.ZMod.Basic

/-! # Integral Schur basis checks -/
namespace SymmetricFunction.Examples

noncomputable section
open SymmetricFunctions SymmetricFunctions.Partition
variable {R : Type*} [CommRing R]
attribute [local irreducible] SymmetricFunction

example : Module.Basis (Nat.Partition 3) (ZMod 6) (homogeneousSubmodule (ZMod 6) 3) :=
  schurBasis (ZMod 6) 3
example : Module.Basis (Nat.Partition 3) PUnit (homogeneousSubmodule PUnit 3) :=
  schurBasis PUnit 3
example : schurBasisAll R ⟨0, default⟩ = 1 := by simp

private def shape22 : Nat.Partition 4 :=
  Partition.union (Nat.Partition.indiscrete 2) (Nat.Partition.indiscrete 2)

private theorem sorted_shape22 : shape22.parts.sort (· ≥ ·) = [2, 2] := by
  norm_num [shape22, Partition.union, Multiset.sort_cons]

private theorem row_shape22 (i : Fin 2) : rowLength shape22 i = 2 := by
  have hr := rowLength_eq_getElem_sort shape22 i (by
    simpa [length, shape22, Partition.union] using i.isLt)
  fin_cases i <;> simpa only [sorted_shape22, List.getElem_cons_succ,
    List.getElem_cons_zero] using hr

-- Repeated rows do not collapse the determinant or change its basis label.
example : schurBasisAll R ⟨4, shape22⟩ = h 2 ^ 2 - h 3 * h 1 := by
  rw [schurBasisAll_apply, ← det_jacobiTrudiMatrix shape22 (L := 2)
    (by simp [length, shape22, Partition.union]), Matrix.det_fin_two]
  have h0 : rowLength shape22 0 = 2 := row_shape22 0
  have h1 : rowLength shape22 1 = 2 := row_shape22 1
  norm_num [jacobiTrudiMatrix, h0, h1, completeInt, pow_two]

-- The ordering statistic is not homogeneous degree.
example : squareWeight shape22 = 8 := by norm_num [squareWeight, shape22, Partition.union]
example : IsHomogeneous (schur (R := R) shape22) 4 := isHomogeneous_schur _

-- Equal-statistic distinct partitions have zero off-diagonal coefficient.
example {d : ℕ} (μ ξ : Nat.Partition d) (hne : μ ≠ ξ)
    (hs : squareWeight μ = squareWeight ξ) : schurCompleteTransition R d μ ξ = 0 := by
  rw [schurCompleteTransition_eq_delta_of_le μ ξ hs.le, ite_eq_right hne]

example (d : ℕ) : (schurCompleteTransition (ZMod 6) d).det = 1 :=
  det_schurCompleteTransition _ _

end
end SymmetricFunction.Examples
