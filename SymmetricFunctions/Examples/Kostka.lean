import SymmetricFunctions.Schur.Kostka
import SymmetricFunctions.Schur.Column
import Mathlib.Data.ZMod.Basic

/-! # Fixed contents, dominance, and the two standard tableaux of shape (2,1) -/
noncomputable section
namespace SymmetricFunction.Examples.Kostka
open SymmetricFunctions SymmetricFunctions.Partition
open scoped BigOperators
variable {R : Type*} [CommRing R]

example (ξ : Nat.Partition 0) : kostka ξ ξ = 1 := by simp
example (ξ : Nat.Partition 0) : FiniteTableau.contentCount ξ (rowContent ξ 0) = 1 := by
  exact FiniteTableau.contentCount_diagonal ξ (by simp)
example (ξ : Nat.Partition 4) :
    schur (R := ZMod 6) ξ = ∑ ν : Nat.Partition 4, (kostka ξ ν : ZMod 6) • mPart ν :=
  schur_eq_sum_kostka_mPart ξ
example (ξ μ : Nat.Partition 4) :
    FiniteTableau.contentCount ξ (rowContent μ 7) = kostka ξ μ :=
  contentCount_rowContent ξ μ ((parts_card_le μ).trans (by decide))

-- Three identical letters in a single row give exactly one tableau.
example : FiniteTableau.contentCount (Nat.Partition.indiscrete 3)
    (rowContent (Nat.Partition.indiscrete 3) 1) = 1 := by
  exact FiniteTableau.contentCount_diagonal _ (by simp)

-- A strict column cannot have the content of a single row.
example : kostka (Nat.Partition.indiscrete 3).conjugate (Nat.Partition.indiscrete 3) = 0 := by
  apply kostka_eq_zero_of_not_dominates
  intro h
  have := (dominates_iff_prefix_rows _ _).mp h 1
  norm_num only [Finset.sum_range_one, rowLength_indiscrete_conjugate,
    rowLength_indiscrete, ite_true] at this

private def shape21 : Nat.Partition 3 := Nat.Partition.ofSums 3 {2, 1} (by decide)

private theorem sorted_shape21 : shape21.parts.sort (· ≥ ·) = [2, 1] := by
  norm_num [shape21, Nat.Partition.ofSums, Multiset.sort_cons, Multiset.filter_singleton]

private theorem row0_shape21 : rowLength shape21 0 = 2 := by
  simpa only [sorted_shape21, List.getElem_cons_zero] using
    rowLength_eq_getElem_sort shape21 0 (by decide)

private theorem row1_shape21 : rowLength shape21 1 = 1 := by
  simpa only [sorted_shape21, List.getElem_cons_succ, List.getElem_cons_zero] using
    rowLength_eq_getElem_sort shape21 1 (by decide)

private theorem schur_shape21 : schur (R := R) shape21 = h 2 * h 1 - h 3 := by
  rw [← det_jacobiTrudiMatrix shape21 (L := 2) (by decide), Matrix.det_fin_two]
  norm_num [jacobiTrudiMatrix, row0_shape21, row1_shape21, completeInt]

/-- Exponent of x₁x₂x₃; the Lean alphabet entries are 0,1,2. -/
private def squarefreeThree : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => 1)

private theorem coefficient_two :
    (alphabetSpecialization R (Fin 3) (schur shape21)).coeff squarefreeThree = 2 := by
  classical
  rw [schur_shape21, map_sub, map_mul, alphabetSpecialization_h,
    alphabetSpecialization_h, alphabetSpecialization_h, MvPolynomial.hsymm_one,
    Fin.sum_univ_three, mul_add, mul_add]
  simp only [MvPolynomial.coeff_sub, AddMonoidAlgebra.coeff_add]
  simp only [Finsupp.add_apply]
  simp only [MvPolynomial.coeff_mul_X', coeff_hsymm]
  norm_num [squarefreeThree, Finsupp.degree_eq_sum, Fin.sum_univ_three,
    Finsupp.sub_apply, Finsupp.single_apply]

-- Both the polynomial coefficient and the actual finite tableau count are two.
example : (alphabetSpecialization (ZMod 6) (Fin 3) (schur shape21)).coeff
    squarefreeThree = 2 := coefficient_two
example : FiniteTableau.contentCount shape21 squarefreeThree = 2 := by
  apply Nat.cast_injective (R := ℤ)
  rw [← coeff_alphabetSpecialization_schur]
  exact coefficient_two

example : kostka shape21 (Nat.Partition.indiscrete 3).conjugate = 2 := by
  have he : rowContent (Nat.Partition.indiscrete 3).conjugate 3 = squarefreeThree := by
    ext i
    simp [rowContent_apply, rowLength_indiscrete_conjugate, squarefreeThree, i.isLt]
  change FiniteTableau.contentCount shape21 _ = 2
  rw [he]
  apply Nat.cast_injective (R := ℤ)
  rw [← coeff_alphabetSpecialization_schur]
  exact coefficient_two

-- Repeated partition content has diagonal coefficient one, without an orbit factor.
example : (alphabetSpecialization R (Fin 3) (schur shape21)).coeff
    (rowContent shape21 3) = 1 := by
  rw [coeff_schur_eq_kostka _ _ _ (exponentParts_rowContent _ (parts_card_le _))]
  simp

end SymmetricFunction.Examples.Kostka
