import SymmetricFunctions.Hopf.MixedSpecialization
import SymmetricFunctions.Finite.SeparatedColumns
import Mathlib.Order.Interval.Finset.Fin

/-! # Integral skew Jacobi–Trudi via an actual mixed alphabet -/

noncomputable section
namespace SymmetricFunctions.Partition

/-- Matching two decreasing sequences by a permutation cannot improve any sorted coordinate. -/
theorem antitone_le_of_perm {N : ℕ} {a b : Fin N → ℕ}
    (ha : Antitone a) (hb : Antitone b) (σ : Equiv.Perm (Fin N))
    (hab : ∀ i, b i ≤ a (σ i)) : ∀ i, b i ≤ a i := by
  classical
  intro k
  by_contra hk
  have hmap : Set.MapsTo σ (Finset.Iic k) (Finset.Iio k) := by
    intro i hi
    have hik : i ≤ k := Finset.mem_Iic.mp hi
    apply Finset.mem_Iio.mpr
    by_contra hσ
    have hki : k ≤ σ i := le_of_not_gt hσ
    have := ha hki
    have := hb hik
    have := hab i
    omega
  have hc := Finset.card_le_card_of_injOn σ hmap σ.injective.injOn
  rw [Fin.card_Iic, Fin.card_Iio] at hc
  omega

end SymmetricFunctions.Partition

namespace SymmetricFunction
open SymmetricFunctions SymmetricFunctions.Partition
variable {R : Type*} [CommRing R]

/-- Integer complete indices expressed as a zero-extended natural difference. -/
theorem completeInt_sub (k r : ℕ) :
    completeInt (R := R) ((k : ℤ) - (r : ℤ)) = if r ≤ k then h (k - r) else 0 := by
  by_cases hr : r ≤ k
  · rw [show (k : ℤ) - (r : ℤ) = ((k - r : ℕ) : ℤ) by omega]
    simp only [completeInt_natCast, ite_eq_left hr]
  · exact (completeInt_of_neg (by omega)).trans (ite_eq_right hr).symm

/-- One column of the mixed alternant factorization, with a finite degree bound. -/
def mixedCompleteColumn {N : ℕ} (j : Fin N) (k : ℕ) : MvPolynomial (Fin N) (SymmetricFunction R) :=
  ∑ r : Fin (k + 1), MvPolynomial.C (h (k - r.val)) * MvPolynomial.X j ^ r.val

/-- The left complete series times a single-variable geometric series has finite coefficients. -/
theorem coeff_left_complete_geometric {N : ℕ} (j : Fin N) (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.map MvPolynomial.C (completeGeneratingSeries (R := R)) *
      PowerSeries.mk (fun r => MvPolynomial.X j ^ r)) = mixedCompleteColumn j k := by
  rw [mul_comm, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_map, coeff_completeGeneratingSeries]
  rw [mixedCompleteColumn,
    Fin.sum_univ_eq_sum_range (fun r : ℕ =>
      MvPolynomial.C (h (R := R) (k - r)) * MvPolynomial.X j ^ r)]
  apply Finset.sum_congr rfl
  intro r _
  exact mul_comm _ _

/-- Evaluating an integer complete index is coefficient extraction after zero extension. -/
theorem sumAlphabetSpecialization_completeInt_sub (N k r : ℕ) :
    sumAlphabetSpecialization R N (completeInt ((k : ℤ) - (r : ℤ))) =
      if r ≤ k then PowerSeries.coeff (k - r)
        (PowerSeries.map (sumAlphabetSpecialization R N).toRingHom completeGeneratingSeries)
      else 0 := by
  rw [completeInt_sub]
  split_ifs <;> simp

/-- The omitted-variable matrix also factors the complete matrix of a sum alphabet. -/
theorem mixed_complete_matrix_mul (N : ℕ) (a : Fin N → ℕ) :
    Matrix.of (fun i j : Fin N => sumAlphabetSpecialization R N
      (completeInt ((a i : ℤ) - ((N - 1 - j.val : ℕ) : ℤ)))) *
        completeEvaluationMatrix (R := SymmetricFunction R) N =
      Matrix.of (fun i j : Fin N => mixedCompleteColumn (R := R) j (a i)) := by
  funext i j
  rw [Matrix.mul_apply]
  change (∑ k : Fin N, sumAlphabetSpecialization R N
    (completeInt ((a i : ℤ) - ((N - 1 - k.val : ℕ) : ℤ))) *
      (elementaryWithout j).coeff (N - 1 - k.val)) = mixedCompleteColumn j (a i)
  have hre := Equiv.sum_comp Fin.revPerm (fun r : Fin N =>
    sumAlphabetSpecialization R N (completeInt ((a i : ℤ) - (r.val : ℤ))) *
      (elementaryWithout (R := SymmetricFunction R) j).coeff r.val)
  have hre' : (∑ k : Fin N, sumAlphabetSpecialization R N
      (completeInt ((a i : ℤ) - ((N - 1 - k.val : ℕ) : ℤ))) *
        (elementaryWithout j).coeff (N - 1 - k.val)) =
      ∑ r : Fin N, sumAlphabetSpecialization R N
        (completeInt ((a i : ℤ) - (r.val : ℤ))) * (elementaryWithout j).coeff r.val := by
    simpa only [Fin.revPerm_apply, Fin.val_rev, Nat.sub_sub, Nat.add_comm] using hre
  rw [hre']
  simp_rw [sumAlphabetSpecialization_completeInt_sub]
  rw [sum_finite_coeff_mul _ _ (natDegree_elementaryWithout_lt j),
    sumAlphabetSpecialization_completeSeries, mul_assoc,
    completeSeries_mul_elementaryWithout, coeff_left_complete_geometric]

/-- Mixed-alphabet Jacobi–Trudi factors through a matrix of independent column polynomials. -/
theorem mixed_jacobiTrudi_mul_completeEvaluationMatrix {d : ℕ}
    (ξ : Nat.Partition d) (N : ℕ) :
    (jacobiTrudiMatrix (R := R) ξ N).map (sumAlphabetSpecialization R N) *
      completeEvaluationMatrix (R := SymmetricFunction R) N =
        Matrix.of (fun i j : Fin N => mixedCompleteColumn (R := R) j (shiftedRows ξ N i)) := by
  have he := mixed_complete_matrix_mul (R := R) N (shiftedRows ξ N)
  convert he using 2
  funext i j
  apply congrArg (sumAlphabetSpecialization R N)
  apply congrArg (completeInt (R := R))
  simp only [shiftedRows_apply]
  have hi := i.isLt
  have hj := j.isLt
  omega

/-- A division-free mixed bialternant identity over the original coefficient ring. -/
theorem mixed_bialternant_schur {d N : ℕ} (ξ : Nat.Partition d) (hN : length ξ ≤ N) :
    sumAlphabetSpecialization R N (schur ξ) *
      staircaseAlternant (R := SymmetricFunction R) N =
        (Matrix.of (fun i j : Fin N =>
          mixedCompleteColumn (R := R) j (shiftedRows ξ N i))).det := by
  have he := congrArg Matrix.det
    (mixed_jacobiTrudi_mul_completeEvaluationMatrix (R := R) ξ N)
  have hm := (sumAlphabetSpecialization R N).map_det (jacobiTrudiMatrix ξ N)
  change sumAlphabetSpecialization R N (jacobiTrudiMatrix ξ N).det =
    ((jacobiTrudiMatrix ξ N).map (sumAlphabetSpecialization R N)).det at hm
  rw [Matrix.det_mul, ← hm, det_jacobiTrudiMatrix ξ hN,
    det_completeEvaluationMatrix] at he
  exact he

/-- The skew Jacobi–Trudi formula for the Hall-adjoint definition, with sufficient
zero padding for both shapes. All index subtraction takes place in the integers. -/
theorem skew_jacobiTrudi {d e N : ℕ} (ξ : Nat.Partition d) (μ : Nat.Partition e)
    (hξ : length ξ ≤ N) (hμ : length μ ≤ N) :
    (skewJacobiTrudiMatrix (R := R) ξ μ N).det = skewSchur ξ μ := by
  classical
  rw [skewSchur_eq_mixed_coeff R ξ μ hμ, mul_comm,
    mixed_bialternant_schur ξ hξ]
  simp only [mixedCompleteColumn]
  rw [coeff_det_separated (fun i => shiftedRows ξ N i)
    (fun i _ r => h (R := R) (shiftedRows ξ N i - r)) (shiftedRows μ N)]
  congr 1
  funext i j
  change completeInt _ = if shiftedRows μ N j ≤ shiftedRows ξ N i then
    h (shiftedRows ξ N i - shiftedRows μ N j) else 0
  rw [← completeInt_sub]
  apply congrArg (completeInt (R := R))
  simp only [shiftedRows_apply]
  have hi := i.isLt
  have hj := j.isLt
  omega

/-- The adjoint skew function vanishes for noncontained Young diagrams, even when
size comparison alone cannot detect noncontainment. -/
theorem skewSchur_eq_zero_of_not_contained {d e : ℕ}
    (ξ : Nat.Partition d) (μ : Nat.Partition e) (hμξ : ¬ Contained μ ξ) :
    skewSchur (R := R) ξ μ = 0 := by
  classical
  let N := max (length ξ) (length μ)
  have hξ : length ξ ≤ N := le_max_left _ _
  have hμ : length μ ≤ N := le_max_right _ _
  rw [← skew_jacobiTrudi ξ μ hξ hμ, Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ _
  have hn : ¬ ∀ i : Fin N, shiftedRows μ N i ≤ shiftedRows ξ N (σ i) := by
    intro he
    have hs := antitone_le_of_perm (shiftedRows_strictAnti ξ).antitone
      (shiftedRows_strictAnti μ).antitone σ he
    apply hμξ
    rw [contained_iff_rowLength]
    intro i
    by_cases hi : i < N
    · have := hs ⟨i, hi⟩
      simpa only [shiftedRows_apply, Nat.add_le_add_iff_right] using this
    · rw [rowLength_eq_zero μ (hμ.trans (by omega))]
      exact Nat.zero_le _
  obtain ⟨i, hi⟩ := not_forall.mp hn
  have hz : skewJacobiTrudiMatrix (R := R) ξ μ N (σ i) i = 0 := by
    apply completeInt_of_neg
    simp only [shiftedRows_apply] at hi
    have hiN := i.isLt
    have hσN := (σ i).isLt
    omega
  have hp : (∏ j : Fin N, skewJacobiTrudiMatrix (R := R) ξ μ N (σ j) j) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hz
  rw [hp, smul_zero]

end SymmetricFunction
