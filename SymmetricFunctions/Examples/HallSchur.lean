import SymmetricFunctions.Hall.Schur
import Mathlib.Data.ZMod.Basic

/-! # Actual Schur determinant orthogonality, including torsion coefficients -/

noncomputable section
namespace SymmetricFunction.Examples
open SymmetricFunctions SymmetricFunctions.Partition
variable {R : Type*} [CommRing R]

private def hallShape21 : Nat.Partition 3 := Nat.Partition.ofSums 3 {2, 1} (by decide)

example : hall (schur (R := ZMod 6) hallShape21) (schur hallShape21) = 1 := by
  simpa using hall_schur_schur (R := ZMod 6) ⟨3, hallShape21⟩ ⟨3, hallShape21⟩

example : hall (schur (R := R) hallShape21) (schur (Nat.Partition.indiscrete 3)) = 0 := by
  have hn : (⟨3, hallShape21⟩ : Σ d, Nat.Partition d) ≠ ⟨3, Nat.Partition.indiscrete 3⟩ := by
    intro he
    have hp := congrArg (fun ξ : Σ d, Nat.Partition d => ξ.2.parts.card) he
    norm_num [hallShape21, Nat.Partition.ofSums, Multiset.filter_singleton] at hp
  simpa only [ite_eq_right hn] using
    hall_schur_schur (R := R) ⟨3, hallShape21⟩ ⟨3, Nat.Partition.indiscrete 3⟩

-- Empty determinant and empty alphabet are included in the general bialternant identity.
example (ξ : Nat.Partition 0) :
    alphabetSpecialization R (Fin 0) (schur ξ) * staircaseAlternant 0 =
      partitionAlternant ξ 0 := bialternant_schur ξ (by simp)

-- Extra zero padding does not alter the coefficient functional.
example (f : SymmetricFunction R) :
    hall (schur hallShape21) f =
      (staircaseAlternant 7 * alphabetSpecialization R (Fin 7) f).coeff
        (shiftedRows hallShape21 7) :=
  hall_schur_eq_alternating_coeff hallShape21 (by decide) f

-- Negative determinant indices agree with impossible monomial divisibility.
example (f : SymmetricFunction R) :
    hall (∏ _i : Fin 1, completeInt ((0 : ℤ) - 1)) f = 0 := by simp

example {d : ℕ} (ξ μ : Nat.Partition d) :
    hallHomogeneous PUnit d (schurBasis PUnit d ξ) (schurBasis PUnit d μ) =
      if ξ = μ then 1 else 0 := hallHomogeneous_schurBasis d ξ μ

example (ξ : Σ d, Nat.Partition d) (f : SymmetricFunction (ZMod 6)) :
    hall (schur ξ.2) f = (schurBasisAll (ZMod 6)).repr f ξ := hall_schur ξ f

end SymmetricFunction.Examples
