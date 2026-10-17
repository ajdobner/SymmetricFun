import SymmetricFunctions.Schur.Branching
import SymmetricFunctions.Tableaux.Skew

/-! # Bridges between the actual skew determinant and actual tableau sums -/
noncomputable section
namespace SymmetricFunction
open SymmetricFunctions.Partition
variable {R : Type*} [CommRing R]

/-- The one-letter case of the skew tableau formula, including empty/noncontained shapes. -/
theorem alphabetSpecialization_one_skewSchur_eq_tableaux {d e : ℕ}
    (ξ : Nat.Partition d) (μ : Nat.Partition e) :
    alphabetSpecialization R (Fin 1) (skewSchur ξ μ) =
      SkewTableau.generatingPolynomial ξ μ 1 R := by
  classical
  rw [alphabetSpecialization_one_skewSchur, SkewTableau.generatingPolynomial_one]

end SymmetricFunction
