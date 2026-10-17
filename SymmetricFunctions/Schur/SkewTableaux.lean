import SymmetricFunctions.Schur.Branching
import SymmetricFunctions.Tableaux.SkewBranching

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

/-- The actual skew function and actual tableau sum both have the correct zero-alphabet value. -/
theorem alphabetSpecialization_zero_skewSchur_eq_tableaux {d e : ℕ}
    (ξ : Nat.Partition d) (μ : Nat.Partition e) :
    alphabetSpecialization R (Fin 0) (skewSchur ξ μ) =
      SkewTableau.generatingPolynomial ξ μ 0 R := by
  by_cases hc : Contained μ ξ
  · by_cases he : d = e
    · subst e
      have hd : YoungDiagram.ofPartition μ = YoungDiagram.ofPartition ξ := by
        apply YoungDiagram.ext
        apply Finset.eq_of_subset_of_card_le hc
        simp only [YoungDiagram.card_ofPartition, le_refl]
      have hp : μ = ξ := ext_rowLength (fun i => congrArg (fun D : YoungDiagram => D.rowLen i) hd)
      subst μ
      simp
    · have hlt : e < d := lt_of_le_of_ne hc.size_le (Ne.symm he)
      rw [SkewTableau.generatingPolynomial_zero_alphabet R hlt]
      have hh : (alphabetSpecialization R (Fin 0) (skewSchur ξ μ)).IsHomogeneous (d - e) := by
        rw [alphabetSpecialization_fin]
        exact isHomogeneous_rho R 0 (d - e) _ (isHomogeneous_skewSchur ξ μ)
      apply MvPolynomial.ext
      intro a
      have ha : a = 0 := Subsingleton.elim _ _
      subst a
      change (alphabetSpecialization R (Fin 0) (skewSchur ξ μ)).coeff 0 = 0
      exact hh.coeff_eq_zero (by simp; omega)
  · rw [skewSchur_eq_zero_of_not_contained ξ μ hc, map_zero,
      SkewTableau.generatingPolynomial_eq_zero_of_not_contained R hc]

/-- The integral skew tableau formula for the existing Hall-adjoint skew Schur function.
There is no stable-range or containment hypothesis; noncontained pairs give zero. -/
theorem alphabetSpecialization_skewSchur_eq_tableaux {d e : ℕ}
    (ξ : Nat.Partition d) (μ : Nat.Partition e) (N : ℕ) :
    alphabetSpecialization R (Fin N) (skewSchur ξ μ) =
      SkewTableau.generatingPolynomial ξ μ N R := by
  classical
  induction N generalizing d e with
  | zero => exact alphabetSpecialization_zero_skewSchur_eq_tableaux ξ μ
  | succ N ih =>
    rw [alphabetSpecialization_succ_skewSchur, SkewTableau.generatingPolynomial_succ]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro ν hν
    split_ifs <;> simp only [ih]

/-- Every specified-content skew coefficient is a natural tableau count cast into R. -/
theorem coeff_alphabetSpecialization_skewSchur {d e N : ℕ} (ξ : Nat.Partition d)
    (μ : Nat.Partition e) (a : Fin N →₀ ℕ) :
    (alphabetSpecialization R (Fin N) (skewSchur ξ μ)).coeff a =
      (SkewTableau.contentCount ξ μ a : R) := by
  rw [alphabetSpecialization_skewSchur_eq_tableaux, SkewTableau.coeff_generatingPolynomial]

end SymmetricFunction
