import SymmetricFunctions.Schur.Skew
import SymmetricFunctions.Hopf.Series

/-!
# A finite right alphabet with bounded symmetric-function coefficients

The right tensor factor specializes to actual variables. The left tensor factor
remains in the coefficient ring; no rational power-sum evaluation is used.
-/

noncomputable section
open scoped TensorProduct
namespace SymmetricFunctions
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Coefficient change preserves the actual staircase alternant polynomial. -/
@[simp] theorem map_staircaseAlternant (φ : R →+* S) (N : ℕ) :
    MvPolynomial.map φ (staircaseAlternant (R := R) N) = staircaseAlternant (R := S) N := by
  rw [staircaseAlternant, RingHom.map_det]
  congr 1
  funext i j
  simp [alternantMatrix]

end SymmetricFunctions

namespace SymmetricFunction
open SymmetricFunctions SymmetricFunctions.Partition
variable (R : Type*) [CommRing R]

/-- Specialize the right factor and retain the left factor as polynomial coefficients. -/
def rightAlphabetSpecialization (N : ℕ) :
    (SymmetricFunction R ⊗[R] SymmetricFunction R) →ₐ[R]
      MvPolynomial (Fin N) (SymmetricFunction R) :=
  Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom R (SymmetricFunction R) (MvPolynomial (Fin N) (SymmetricFunction R)))
    ((MvPolynomial.mapAlgHom (Algebra.ofId R (SymmetricFunction R))).comp
      (alphabetSpecialization R (Fin N))) (fun _ _ => Commute.all _ _)

@[simp] theorem rightAlphabetSpecialization_tmul (N : ℕ) (f g : SymmetricFunction R) :
    rightAlphabetSpecialization R N (f ⊗ₜ[R] g) =
      MvPolynomial.C f * MvPolynomial.map (algebraMap R (SymmetricFunction R))
        (alphabetSpecialization R (Fin N) g) := by
  simp [rightAlphabetSpecialization, MvPolynomial.algebraMap_eq]

/-- Add a finite alphabet to the retained bounded symmetric alphabet. -/
def sumAlphabetSpecialization (N : ℕ) :
    SymmetricFunction R →ₐ[R] MvPolynomial (Fin N) (SymmetricFunction R) :=
  (rightAlphabetSpecialization R N).comp comultiplication

@[simp] theorem sumAlphabetSpecialization_h (N n : ℕ) :
    sumAlphabetSpecialization R N (h n) =
      ∑ ij ∈ Finset.antidiagonal n,
        MvPolynomial.C (h ij.1) * MvPolynomial.hsymm (Fin N) (SymmetricFunction R) ij.2 := by
  change rightAlphabetSpecialization R N (comultiplication (h n)) = _
  rw [comultiplication_h, map_sum]
  apply Finset.sum_congr rfl
  intro ij _
  rw [rightAlphabetSpecialization_tmul, alphabetSpecialization_h, MvPolynomial.map_hsymm]
  exact congrArg (fun deq : DecidableEq (Fin N) =>
    MvPolynomial.C (h (R := R) ij.1) *
      @MvPolynomial.hsymm (Fin N) (SymmetricFunction R) _ _ deq ij.2)
    (Subsingleton.elim _ _)

/-- The complete series of the sum alphabet is the product of the two complete series. -/
theorem sumAlphabetSpecialization_completeSeries (N : ℕ) :
    PowerSeries.map (sumAlphabetSpecialization R N).toRingHom completeGeneratingSeries =
      PowerSeries.map MvPolynomial.C (completeGeneratingSeries (R := R)) *
        completeSeries (Fin N) (SymmetricFunction R) := by
  apply PowerSeries.ext
  intro n
  simp [PowerSeries.coeff_mul, sumAlphabetSpecialization_h]

/-- Alternating coefficient extraction in the right alphabet is Schur contraction. -/
theorem coeff_rightAlphabetSpecialization_schur {d N : ℕ} (μ : Nat.Partition d)
    (hN : length μ ≤ N) (z : SymmetricFunction R ⊗[R] SymmetricFunction R) :
    (staircaseAlternant N * rightAlphabetSpecialization R N z).coeff (shiftedRows μ N) =
      hallContraction (schur μ) z := by
  induction z with
  | tmul x y =>
    rw [rightAlphabetSpecialization_tmul, hallContraction_tmul]
    rw [← map_staircaseAlternant (algebraMap R (SymmetricFunction R)) N]
    rw [mul_left_comm, ← map_mul, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
      ← hall_schur_eq_alternating_coeff μ hN]
    rw [Algebra.smul_def, mul_comm]
  | add z w hz hw =>
    simpa only [map_add, mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using
      congrArg₂ (· + ·) hz hw

/-- The skew Schur adjoint is an actual finite mixed-alphabet coefficient. -/
theorem skewSchur_eq_mixed_coeff {d e N : ℕ} (ξ : Nat.Partition d) (μ : Nat.Partition e)
    (hN : length μ ≤ N) :
    skewSchur (R := R) ξ μ =
      (staircaseAlternant N * sumAlphabetSpecialization R N (schur ξ)).coeff (shiftedRows μ N) :=
  (coeff_rightAlphabetSpecialization_schur R μ hN (comultiplication (schur ξ))).symm

end SymmetricFunction
