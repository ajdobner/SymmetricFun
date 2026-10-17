import SymmetricFunctions.Schur.Tableaux
import SymmetricFunctions.Schur.Column
import Mathlib.Data.ZMod.Basic

/-! # One-letter determinant/tableau identification and finite branching -/
noncomputable section
namespace SymmetricFunction.Examples
open SymmetricFunctions.Partition
variable {R : Type*} [CommRing R]

example (ξ : Nat.Partition 0) (μ : Nat.Partition 0) :
    alphabetSpecialization R (Fin 1) (skewSchur ξ μ) = 1 := by
  have he : ξ = μ := Subsingleton.elim _ _
  subst μ
  simp

example (ξ : Nat.Partition 5) (μ : Nat.Partition 2) :
    alphabetSpecialization (ZMod 6) (Fin 1) (skewSchur ξ μ) =
      SkewTableau.generatingPolynomial ξ μ 1 (ZMod 6) :=
  alphabetSpecialization_one_skewSchur_eq_tableaux _ _

example : alphabetSpecialization R (Fin 1)
    (skewSchur (Nat.Partition.indiscrete 3) (Nat.Partition.indiscrete 1)) =
      MvPolynomial.X (0 : Fin 1) ^ 2 := by
  classical
  rw [alphabetSpecialization_one_skewSchur]
  have hs : HorizontalStrip (Nat.Partition.indiscrete 1) (Nat.Partition.indiscrete 3) := by
    constructor
    · apply (contained_iff_rowLength _ _).mpr
      intro i
      simp only [rowLength_indiscrete]
      split_ifs <;> omega
    · intro i
      simp [rowLength_indiscrete]
  simp [hs]

example : alphabetSpecialization R (Fin 1)
    (schur (Nat.Partition.indiscrete 2).conjugate) = 0 := by
  classical
  rw [← skewSchur_empty _ (Nat.Partition.indiscrete 0), alphabetSpecialization_one_skewSchur]
  have hs : ¬ HorizontalStrip (Nat.Partition.indiscrete 0)
      (Nat.Partition.indiscrete 2).conjugate := by
    intro h
    have := h.2 0
    simp at this
  simp [hs]

example (ξ : Nat.Partition 3) (μ : Nat.Partition 1) :
    alphabetSpecialization PUnit (Fin 1) (skewSchur ξ μ) = 0 := Subsingleton.elim _ _

-- Every alphabet, without a stable-range bound, including torsion and zero rings.
example (ξ : Nat.Partition 5) (N : ℕ) :
    alphabetSpecialization (ZMod 6) (Fin N) (schur ξ) =
      FiniteTableau.generatingPolynomial ξ N (ZMod 6) :=
  alphabetSpecialization_schur_eq_tableaux _ _
example (ξ : Nat.Partition 5) (μ : Nat.Partition 2) (N : ℕ) :
    alphabetSpecialization PUnit (Fin N) (skewSchur ξ μ) =
      SkewTableau.generatingPolynomial ξ μ N PUnit :=
  alphabetSpecialization_skewSchur_eq_tableaux _ _ _

-- Row tableaux allow repeated entries; column tableaux require strict entries.
example (n N : ℕ) : FiniteTableau.generatingPolynomial (Nat.Partition.indiscrete n) N R =
    (rho R N (h n)).val := by
  rw [← rho_schur_eq_tableaux, schur_indiscrete]
example (n N : ℕ) :
    FiniteTableau.generatingPolynomial (Nat.Partition.indiscrete n).conjugate N R =
      (rho R N (e n)).val := by
  rw [← rho_schur_eq_tableaux, schur_indiscrete_conjugate]
example : alphabetSpecialization R (Fin 0) (schur (Nat.Partition.indiscrete 1)) = 0 := by
  apply alphabetSpecialization_schur_eq_zero_of_length_gt
  simp
example (ξ : Nat.Partition 5) (N : ℕ) :
    zeroLast R N (FiniteTableau.generatingPolynomial ξ (N + 1) R) =
      FiniteTableau.generatingPolynomial ξ N R := zeroLast_tableauGeneratingPolynomial _ _

-- The weight of a restored strip includes one new letter for each removed cell.
example {d e n N : ℕ} {ξ : Nat.Partition d} {μ : Nat.Partition e} {ν : Nat.Partition n}
    (U : SkewTableau ν μ N) (hs : HorizontalStrip ν ξ) :
    SkewTableau.weight R (SkewTableau.extendLargest U hs) =
      MvPolynomial.rename Fin.castSucc (SkewTableau.weight R U) *
        MvPolynomial.X (Fin.last N) ^ (d - n) := SkewTableau.weight_extendLargest _ _ _

end SymmetricFunction.Examples
