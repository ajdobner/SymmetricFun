import SymmetricFunctions.Schur.JacobiTrudi
import SymmetricFunctions.Hall.Symmetry
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Integral bialternants for the Jacobi–Trudi determinants

The identity is multiplicative; no Vandermonde determinant is inverted.
-/

noncomputable section
namespace SymmetricFunctions
variable {R : Type*} [CommRing R]

/-- The elementary generating polynomial with one alphabet variable omitted. -/
def elementaryWithout {N : ℕ} (j : Fin N) : Polynomial (MvPolynomial (Fin N) R) :=
  ∏ i ∈ Finset.univ.erase j, (1 - Polynomial.C (MvPolynomial.X i) * Polynomial.X)

/-- Omitting one variable leaves degree at most N-1 in the series parameter. -/
theorem natDegree_elementaryWithout_lt {N : ℕ} (j : Fin N) :
    (elementaryWithout (R := R) j).natDegree < N := by
  have he (i : Fin N) :
      (1 - Polynomial.C (MvPolynomial.X (R := R) i) * Polynomial.X).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · simpa only [pow_one] using Polynomial.natDegree_C_mul_X_pow_le
        (MvPolynomial.X (R := R) i) 1
  have hd := (Polynomial.natDegree_prod_le (Finset.univ.erase j)
    (fun i : Fin N => 1 - Polynomial.C (MvPolynomial.X (R := R) i) * Polynomial.X)).trans
      (Finset.sum_le_sum (fun i _ => he i))
  change (elementaryWithout (R := R) j).natDegree < N
  apply hd.trans_lt
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  norm_cast
  exact Nat.sub_lt (Nat.zero_lt_of_lt j.isLt) (by decide)

/-- Cancellation of the other geometric factors leaves the selected variable. -/
theorem completeSeries_mul_elementaryWithout {N : ℕ} (j : Fin N) :
    completeSeries (Fin N) R *
      (elementaryWithout (R := R) j : PowerSeries (MvPolynomial (Fin N) R)) =
      PowerSeries.mk (fun n => MvPolynomial.X j ^ n) := by
  let H (i : Fin N) : PowerSeries (MvPolynomial (Fin N) R) :=
    PowerSeries.mk (fun n => MvPolynomial.X i ^ n)
  let E (i : Fin N) : PowerSeries (MvPolynomial (Fin N) R) :=
    1 - PowerSeries.C (MvPolynomial.X i) * PowerSeries.X
  have hi (i : Fin N) : H i * E i = 1 := by
    have he := congrArg (PowerSeries.rescale (MvPolynomial.X (R := R) i))
      (PowerSeries.mk_one_mul_one_sub_eq_one (MvPolynomial (Fin N) R))
    simpa [H, E, PowerSeries.rescale_mk, PowerSeries.rescale_X] using he
  have he : (elementaryWithout (R := R) j : PowerSeries (MvPolynomial (Fin N) R)) =
      ∏ i ∈ Finset.univ.erase j, E i := by
    change Polynomial.coeToPowerSeries.ringHom (∏ i ∈ Finset.univ.erase j,
      (1 - Polynomial.C (MvPolynomial.X i) * Polynomial.X)) = _
    simp [E]
  rw [he]
  change (∏ i : Fin N, H i) * _ = H j
  rw [← Finset.mul_prod_erase Finset.univ H (Finset.mem_univ j), mul_assoc,
    ← Finset.prod_mul_distrib]
  simp [hi]

/-- Convolution with a polynomial can be summed to any bound above its degree. -/
theorem sum_finite_coeff_mul {A : Type*} [CommRing A] (F : PowerSeries A)
    (P : Polynomial A) {N : ℕ} (hP : P.natDegree < N) (k : ℕ) :
    (∑ r : Fin N, (if r.val ≤ k then PowerSeries.coeff (k - r.val) F else 0) * P.coeff r.val) =
      PowerSeries.coeff k (F * (P : PowerSeries A)) := by
  classical
  let u (r : ℕ) := (if r ≤ k then PowerSeries.coeff (k - r) F else 0) * P.coeff r
  have hc : PowerSeries.coeff k (F * (P : PowerSeries A)) =
      ∑ r ∈ Finset.range (k + 1), u r := by
    rw [mul_comm F, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro r hr
    have hrk : r ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hr
    simp [u, hrk, Polynomial.coeff_coe, mul_comm]
  rw [hc]
  change (∑ r : Fin N, u r.val) = _
  rw [Fin.sum_univ_eq_sum_range]
  change ∑ r ∈ Finset.range N, u r = ∑ r ∈ Finset.range (k + 1), u r
  rcases le_total N (k + 1) with hN | hN
  · apply Finset.sum_subset (Finset.range_mono hN)
    intro r hr hrN
    have hNr : N ≤ r := by simpa using hrN
    simp [u, Polynomial.coeff_eq_zero_of_natDegree_lt (hP.trans_le hNr)]
  · symm
    apply Finset.sum_subset (Finset.range_mono hN)
    intro r hr hrk
    have hkr : ¬ r ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hrk
    simp [u, hkr]

/-- Coefficients of the omitted-variable elementary polynomials, in reverse order. -/
def completeEvaluationMatrix (N : ℕ) : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) R) :=
  fun i j => (elementaryWithout j).coeff (N - 1 - i.val)

/-- Monomial alternant matrix for an arbitrary nonnegative exponent sequence. -/
def alternantMatrix {N : ℕ} (a : Fin N → ℕ) :
    Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) R) := fun i j => MvPolynomial.X j ^ a i

/-- A finite complete integer index expressed without truncated subtraction. -/
theorem finiteCompleteInt_sub (N k r : ℕ) :
    SymmetricFunction.finiteCompleteInt (R := R) N ((k : ℤ) - (r : ℤ)) =
      if r ≤ k then MvPolynomial.hsymm (Fin N) R (k - r) else 0 := by
  by_cases hr : r ≤ k
  · rw [show (k : ℤ) - (r : ℤ) = ((k - r : ℕ) : ℤ) by omega]
    simp [SymmetricFunction.finiteCompleteInt, hr]
  · have hn : ¬ 0 ≤ (k : ℤ) - (r : ℤ) := by omega
    simp only [SymmetricFunction.finiteCompleteInt, ite_eq_right hn, ite_eq_right hr]

/-- The complete matrix factors each alternant without any division. -/
theorem complete_matrix_mul (N : ℕ) (a : Fin N → ℕ) :
    Matrix.of (fun i j : Fin N => SymmetricFunction.finiteCompleteInt (R := R) N
      ((a i : ℤ) - ((N - 1 - j.val : ℕ) : ℤ))) * completeEvaluationMatrix (R := R) N =
        alternantMatrix a := by
  funext i j
  rw [Matrix.mul_apply]
  change (∑ k : Fin N, SymmetricFunction.finiteCompleteInt (R := R) N
    ((a i : ℤ) - ((N - 1 - k.val : ℕ) : ℤ)) *
      (elementaryWithout j).coeff (N - 1 - k.val)) = MvPolynomial.X j ^ a i
  have hre := Equiv.sum_comp Fin.revPerm (fun r : Fin N =>
    SymmetricFunction.finiteCompleteInt (R := R) N ((a i : ℤ) - (r.val : ℤ)) *
      (elementaryWithout (R := R) j).coeff r.val)
  have hre' : (∑ k : Fin N, SymmetricFunction.finiteCompleteInt (R := R) N
      ((a i : ℤ) - ((N - 1 - k.val : ℕ) : ℤ)) *
        (elementaryWithout j).coeff (N - 1 - k.val)) =
      ∑ r : Fin N, SymmetricFunction.finiteCompleteInt (R := R) N
        ((a i : ℤ) - (r.val : ℤ)) * (elementaryWithout j).coeff r.val := by
    simpa only [Fin.revPerm_apply, Fin.val_rev, Nat.sub_sub, Nat.add_comm] using hre
  rw [hre']
  simp_rw [finiteCompleteInt_sub, ← coeff_completeSeries (Fin N) R]
  rw [sum_finite_coeff_mul _ _ (natDegree_elementaryWithout_lt j),
    completeSeries_mul_elementaryWithout, PowerSeries.coeff_mk]

/-- The staircase alternant, with decreasing row exponents. -/
def staircaseAlternant (N : ℕ) : MvPolynomial (Fin N) R :=
  (alternantMatrix (fun i : Fin N => N - 1 - i.val)).det

/-- The alternant with the partition rows added to the staircase. -/
def partitionAlternant {d : ℕ} (ξ : Nat.Partition d) (N : ℕ) : MvPolynomial (Fin N) R :=
  (alternantMatrix (fun i : Fin N => Partition.rowLength ξ i + (N - 1 - i.val))).det

end SymmetricFunctions

namespace SymmetricFunction
open SymmetricFunctions SymmetricFunctions.Partition
variable {R : Type*} [CommRing R]

/-- Finite specialization of a padded Jacobi–Trudi matrix is entrywise. -/
theorem alphabetSpecialization_det_jacobiTrudi {d : ℕ} (ξ : Nat.Partition d) (N : ℕ) :
    alphabetSpecialization R (Fin N) (jacobiTrudiMatrix ξ N).det =
      (Matrix.of (fun i j : Fin N => finiteCompleteInt (R := R) N
        ((rowLength ξ i : ℤ) - (i : ℤ) + (j : ℤ)))).det := by
  rw [AlgHom.map_det]
  congr 1
  funext i j
  exact (alphabetSpecialization_fin R N _).trans (rho_completeInt N _)

/-- Multiply the actual finite Jacobi–Trudi matrix by the universal coefficient matrix. -/
theorem jacobiTrudi_mul_completeEvaluationMatrix {d : ℕ} (ξ : Nat.Partition d) (N : ℕ) :
    Matrix.of (fun i j : Fin N => finiteCompleteInt (R := R) N
      ((rowLength ξ i : ℤ) - (i : ℤ) + (j : ℤ))) * completeEvaluationMatrix N =
        alternantMatrix (fun i : Fin N => rowLength ξ i + (N - 1 - i.val)) := by
  have he := complete_matrix_mul (R := R) N
    (fun i : Fin N => rowLength ξ i + (N - 1 - i.val))
  convert he using 2
  funext i j
  apply congrArg (finiteCompleteInt (R := R) N)
  have hi := i.isLt
  have hj := j.isLt
  omega

/-- The coefficient matrix has exactly the staircase determinant. -/
theorem det_completeEvaluationMatrix (N : ℕ) :
    (completeEvaluationMatrix (R := R) N).det = staircaseAlternant N := by
  let ξ : Nat.Partition 0 := Nat.Partition.indiscrete 0
  have he := congrArg Matrix.det (jacobiTrudi_mul_completeEvaluationMatrix (R := R) ξ N)
  rw [Matrix.det_mul, ← alphabetSpecialization_det_jacobiTrudi,
    det_jacobiTrudiMatrix ξ (by simp [ξ]), schur_zero, map_one, one_mul] at he
  simpa only [rowLength_zero, zero_add, staircaseAlternant] using he

/-- The integral bialternant formula for the existing Schur determinant.
It is a multiplication identity, valid without a nonzero Vandermonde assumption. -/
theorem bialternant_schur {d N : ℕ} (ξ : Nat.Partition d) (hN : length ξ ≤ N) :
    alphabetSpecialization R (Fin N) (schur ξ) * staircaseAlternant N =
      partitionAlternant ξ N := by
  have he := congrArg Matrix.det (jacobiTrudi_mul_completeEvaluationMatrix (R := R) ξ N)
  rw [Matrix.det_mul, ← alphabetSpecialization_det_jacobiTrudi,
    det_jacobiTrudiMatrix ξ hN, det_completeEvaluationMatrix] at he
  exact he

end SymmetricFunction
