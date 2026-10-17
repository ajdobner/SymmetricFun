import SymmetricFunctions.Tableaux.Basic
import Mathlib.Data.ZMod.Basic

/-! # Actual finite tableau conventions, independent of a Schur formula -/
noncomputable section
namespace SymmetricFunctions.Partition.Examples
open FiniteTableau

example (ξ : Nat.Partition 0) : Fintype.card (FiniteTableau ξ 0) = 1 := by simp
example (ξ : Nat.Partition 0) : generatingPolynomial ξ 0 ℤ = 1 := by simp
example (ξ : Nat.Partition 0) : contentCount ξ (0 : Fin 0 →₀ ℕ) = 1 := by simp
example (ξ : Nat.Partition 3) : generatingPolynomial ξ 0 (ZMod 6) = 0 :=
  generatingPolynomial_zero_alphabet _ (by decide)

-- A row can repeat its sole alphabet letter. No outside-shape zero is counted.
private def rowThree : FiniteTableau (Nat.Partition.indiscrete 3) 1 :=
  highestWeight _ (by simp)

example : content rowThree = Finsupp.single 0 3 := by
  apply content_eq_single_of_constant
  intro c
  exact Subsingleton.elim _ _

example : weight (ZMod 6) rowThree = MvPolynomial.X (0 : Fin 1) ^ 3 := by
  rw [weight, content_eq_single_of_constant rowThree 0 (fun _ => Subsingleton.elim _ _)]
  exact MvPolynomial.X_pow_eq_monomial.symm

-- A column of height three cannot be filled strictly from two letters.
example : IsEmpty (FiniteTableau (Nat.Partition.indiscrete 3).conjugate 2) := by
  apply isEmpty_of_length_gt
  rw [length_conjugate, rowLength_indiscrete]
  decide

example (ξ : Nat.Partition 4) (T : FiniteTableau ξ 3) : T.content.degree = 4 := by simp
example (ξ : Nat.Partition 4) (a : Fin 3 →₀ ℕ) :
    0 ≤ (generatingPolynomial ξ 3 ℤ).coeff a := by
  rw [coeff_generatingPolynomial]
  exact Nat.cast_nonneg _
example (ξ : Nat.Partition 4) (a : Fin 3 →₀ ℕ) :
    (generatingPolynomial ξ 3 (ZMod 6)).coeff a = (contentCount ξ a : ZMod 6) :=
  coeff_generatingPolynomial _ _ _
example (ξ : Nat.Partition 4) : generatingPolynomial ξ 3 PUnit = 0 :=
  Subsingleton.elim _ _

end SymmetricFunctions.Partition.Examples
