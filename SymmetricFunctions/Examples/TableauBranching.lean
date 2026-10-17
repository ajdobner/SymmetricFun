import SymmetricFunctions.Schur.SkewTableaux
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

end SymmetricFunction.Examples
