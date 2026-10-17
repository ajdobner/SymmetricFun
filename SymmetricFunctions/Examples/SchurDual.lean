import SymmetricFunctions.Schur.Dual
import Mathlib.Data.ZMod.Basic

/-! # Dual determinant and conjugation conventions -/
namespace SymmetricFunction.Examples

noncomputable section
open SymmetricFunctions.Partition
variable {R : Type*} [CommRing R]

example : elementaryInt (R := R) ((0 : ℤ) - 1) = 0 := by simp
example : elementaryInt (R := R) 0 = 1 := by simp
example (ξ : Nat.Partition 0) : (elementaryJacobiTrudiMatrix (R := R) ξ.conjugate 4).det = 1 := by
  rw [dual_jacobiTrudi ξ (by simp), schur_zero]
example (n : ℕ) : omega (schur (R := R) (Nat.Partition.indiscrete n)) =
    schur (Nat.Partition.indiscrete n).conjugate := omega_schur _
example {d : ℕ} (ξ : Nat.Partition d) :
    omega (schur (R := ZMod 6) ξ.conjugate) = schur ξ := by simp

private def selfConjugate21 : Nat.Partition 3 := Nat.Partition.ofSums 3 {2, 1} (by decide)

private theorem sorted_selfConjugate21 : selfConjugate21.parts.sort (· ≥ ·) = [2, 1] := by
  norm_num [selfConjugate21, Nat.Partition.ofSums, Multiset.sort_cons, Multiset.filter_singleton]

private theorem conjugate_selfConjugate21 : selfConjugate21.conjugate = selfConjugate21 := by
  have h0 : rowLength selfConjugate21 0 = 2 := by
    simpa only [sorted_selfConjugate21, List.getElem_cons_zero] using
      rowLength_eq_getElem_sort selfConjugate21 0 (by decide)
  have h1 : rowLength selfConjugate21 1 = 1 := by
    simpa only [sorted_selfConjugate21, List.getElem_cons_succ, List.getElem_cons_zero] using
      rowLength_eq_getElem_sort selfConjugate21 1 (by decide)
  have hm (i j : ℕ) : (i, j) ∈ YoungDiagram.ofPartition selfConjugate21 ↔ i + j < 2 := by
    rw [YoungDiagram.mem_iff_lt_rowLen]
    change j < rowLength selfConjugate21 i ↔ _
    by_cases hi : i = 0
    · subst i
      rw [h0]
      omega
    by_cases hi' : i = 1
    · subst i
      rw [h1]
      omega
    rw [rowLength_eq_zero _ (by change 2 ≤ i; omega)]
    omega
  apply YoungDiagram.equivPartition.symm.injective
  apply Subtype.ext
  change YoungDiagram.ofPartition selfConjugate21.conjugate = _
  rw [ofPartition_conjugate]
  ext ⟨i, j⟩
  change (i, j) ∈ (YoungDiagram.ofPartition selfConjugate21).transpose ↔
    (i, j) ∈ YoungDiagram.ofPartition selfConjugate21
  simp only [YoungDiagram.mem_transpose, Prod.swap_prod_mk, hm]
  omega

-- The nontrivial self-conjugate shape (2,1) is fixed, also with torsion coefficients.
example : omega (schur (R := ZMod 6) selfConjugate21) = schur selfConjugate21 := by
  rw [omega_schur, conjugate_selfConjugate21]

end
end SymmetricFunction.Examples
