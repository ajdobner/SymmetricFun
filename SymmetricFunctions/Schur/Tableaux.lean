import SymmetricFunctions.Schur.SkewTableaux

/-! # The integral tableau formula for the actual Jacobi–Trudi Schur functions -/
noncomputable section
namespace SymmetricFunction
open SymmetricFunctions.Partition
variable {R : Type*} [CommRing R]

/-- The genuine bounded Mathlib tableau sum is the specialization of the existing determinant. -/
theorem alphabetSpecialization_schur_eq_tableaux {d : ℕ} (ξ : Nat.Partition d) (N : ℕ) :
    alphabetSpecialization R (Fin N) (schur ξ) = FiniteTableau.generatingPolynomial ξ N R := by
  simpa only [skewSchur_empty, SkewTableau.generatingPolynomial_empty] using
    alphabetSpecialization_skewSchur_eq_tableaux (R := R) ξ (Nat.Partition.indiscrete 0) N

/-- The same theorem through the symmetric-subalgebra specialization API. -/
theorem rho_schur_eq_tableaux {d : ℕ} (ξ : Nat.Partition d) (N : ℕ) :
    (rho R N (schur ξ)).val = FiniteTableau.generatingPolynomial ξ N R := by
  rw [← alphabetSpecialization_fin, alphabetSpecialization_schur_eq_tableaux]

/-- The coefficient of one specified content is a natural count, with no orbit factor. -/
theorem coeff_alphabetSpecialization_schur {d N : ℕ} (ξ : Nat.Partition d)
    (a : Fin N →₀ ℕ) : (alphabetSpecialization R (Fin N) (schur ξ)).coeff a =
      (FiniteTableau.contentCount ξ a : R) := by
  rw [alphabetSpecialization_schur_eq_tableaux, FiniteTableau.coeff_generatingPolynomial]

/-- Alphabet padding is literal zero-last-variable substitution. -/
theorem zeroLast_tableauGeneratingPolynomial {d : ℕ} (ξ : Nat.Partition d) (N : ℕ) :
    zeroLast R N (FiniteTableau.generatingPolynomial ξ (N + 1) R) =
      FiniteTableau.generatingPolynomial ξ N R := by
  rw [← rho_schur_eq_tableaux, ← rho_schur_eq_tableaux, zeroLast_rho]

/-- Skew tableau sums have the same alphabet-padding compatibility. -/
theorem zeroLast_skewTableauGeneratingPolynomial {d e : ℕ} (ξ : Nat.Partition d)
    (μ : Nat.Partition e) (N : ℕ) :
    zeroLast R N (SkewTableau.generatingPolynomial ξ μ (N + 1) R) =
      SkewTableau.generatingPolynomial ξ μ N R := by
  rw [← alphabetSpecialization_skewSchur_eq_tableaux,
    ← alphabetSpecialization_skewSchur_eq_tableaux,
    alphabetSpecialization_fin, alphabetSpecialization_fin, zeroLast_rho]

/-- Too many rows forces zero, for every alphabet size and every coefficient ring. -/
theorem alphabetSpecialization_schur_eq_zero_of_length_gt {d N : ℕ} (ξ : Nat.Partition d)
    (hN : N < length ξ) : alphabetSpecialization R (Fin N) (schur ξ) = 0 := by
  rw [alphabetSpecialization_schur_eq_tableaux,
    FiniteTableau.generatingPolynomial_eq_zero_of_length_gt R hN]

/-- Integral straight coefficients are nonnegative integers. -/
theorem coeff_schur_nonneg {d N : ℕ} (ξ : Nat.Partition d) (a : Fin N →₀ ℕ) :
    0 ≤ (alphabetSpecialization ℤ (Fin N) (schur ξ)).coeff a := by
  rw [coeff_alphabetSpecialization_schur]
  exact Nat.cast_nonneg _

/-- Integral skew monomial coefficients are nonnegative; this does not assert Schur positivity. -/
theorem coeff_skewSchur_nonneg {d e N : ℕ} (ξ : Nat.Partition d) (μ : Nat.Partition e)
    (a : Fin N →₀ ℕ) : 0 ≤ (alphabetSpecialization ℤ (Fin N) (skewSchur ξ μ)).coeff a := by
  rw [coeff_alphabetSpecialization_skewSchur]
  exact Nat.cast_nonneg _

end SymmetricFunction
