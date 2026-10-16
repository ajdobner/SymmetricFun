import SymmetricFunctions.Finite.Bialternant
import Mathlib.Order.Preorder.Finite

/-! # Alternating coefficient extraction for Hall pairing with Schur functions -/

noncomputable section
namespace SymmetricFunctions.Partition

/-- Partition rows shifted by the decreasing staircase of the alphabet size. -/
def shiftedRows {d : ℕ} (ξ : Nat.Partition d) (N : ℕ) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => rowLength ξ i + (N - 1 - i.val))

@[simp] theorem shiftedRows_apply {d N : ℕ} (ξ : Nat.Partition d) (i : Fin N) :
    shiftedRows ξ N i = rowLength ξ i + (N - 1 - i.val) := rfl

/-- Staircase shifting makes the row sequence strictly decreasing. -/
theorem shiftedRows_strictAnti {d N : ℕ} (ξ : Nat.Partition d) :
    StrictAnti (shiftedRows ξ N) := by
  intro i j hij
  have hr := rowLength_antitone ξ (show i.val ≤ j.val by omega)
  have hi := i.isLt
  have hj := j.isLt
  simp only [shiftedRows_apply]
  change i.val < j.val at hij
  omega

/-- Sufficiently padded shifted rows determine the sized partition. -/
theorem shiftedRows_eq_iff (ξ μ : Σ d, Nat.Partition d) {N : ℕ}
    (hξ : length ξ.2 ≤ N) (hμ : length μ.2 ≤ N) :
    shiftedRows ξ.2 N = shiftedRows μ.2 N ↔ ξ = μ := by
  constructor
  · intro he
    have hr (i : ℕ) : rowLength ξ.2 i = rowLength μ.2 i := by
      by_cases hi : i < N
      · have hv := DFunLike.congr_fun he ⟨i, hi⟩
        simpa only [shiftedRows_apply, Nat.add_right_cancel_iff] using hv
      · rw [rowLength_eq_zero _ (hξ.trans (by omega)),
          rowLength_eq_zero _ (hμ.trans (by omega))]
    obtain ⟨d, ξ⟩ := ξ
    obtain ⟨e, μ⟩ := μ
    have hde : d = e := by
      rw [← sum_rowLength_padded ξ hξ, ← sum_rowLength_padded μ hμ]
      exact Finset.sum_congr rfl (fun i _ => hr i)
    subst e
    exact congrArg (Sigma.mk d) (ext_rowLength hr)
  · rintro rfl
    rfl

/-- A permutation matching two strictly decreasing sequences must be the identity. -/
theorem perm_eq_one_of_strictAnti {N : ℕ} {a b : Fin N → ℕ}
    (ha : StrictAnti a) (hb : StrictAnti b) (σ : Equiv.Perm (Fin N))
    (he : ∀ i, b (σ i) = a i) : σ = 1 := by
  have hm : StrictMono σ := by
    intro i j hij
    by_contra h
    have hj : σ j ≤ σ i := le_of_not_gt h
    have hv := hb.antitone hj
    rw [he, he] at hv
    exact (not_le_of_gt (ha hij)) hv
  apply Equiv.ext
  intro i
  exact congrFun hm.eq_id i

end SymmetricFunctions.Partition

namespace SymmetricFunction
open SymmetricFunctions SymmetricFunctions.Partition SymmetricFunctions.Series
variable {R : Type*} [CommRing R]

/-- Negative complete indices and impossible monomial divisibility give the same zero. -/
theorem hall_completeInt_product {N : ℕ} (a b : Fin N →₀ ℕ) (f : SymmetricFunction R) :
    hall (∏ i : Fin N, completeInt ((a i : ℤ) - (b i : ℤ))) f =
      (MvPolynomial.monomial b 1 * alphabetSpecialization R (Fin N) f).coeff a := by
  classical
  rw [MvPolynomial.coeff_monomial_mul']
  by_cases hab : b ≤ a
  · rw [ite_eq_left hab, one_mul]
    have he : (∏ i : Fin N, completeInt (R := R) ((a i : ℤ) - (b i : ℤ))) =
        hPart (exponentPartition (a - b)).2 := by
      rw [hPart_exponentPartition_eq_prod]
      apply Finset.prod_congr rfl
      intro i _
      rw [show (a i : ℤ) - (b i : ℤ) = ((a i - b i : ℕ) : ℤ) by have := hab i; omega,
        completeInt_natCast]
      rfl
    rw [he, hall_hPart_eq_coeff]
  · rw [ite_eq_right hab]
    have hz : (∏ i : Fin N, completeInt (R := R) ((a i : ℤ) - (b i : ℤ))) = 0 := by
      obtain ⟨i, hi⟩ : ∃ i, ¬ b i ≤ a i := by simpa only [Finsupp.le_def, not_forall] using hab
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact completeInt_of_neg (by omega)
    rw [hz, map_zero, LinearMap.zero_apply]

/-- A full finite-variable product is its exponent monomial, including zero entries. -/
theorem prod_X_pow_eq_monomial_all {N : ℕ} (a : Fin N →₀ ℕ) :
    (∏ i : Fin N, MvPolynomial.X (R := R) i ^ a i) = MvPolynomial.monomial a 1 := by
  rw [MvPolynomial.prod_X_pow]
  have he : Finsupp.indicator Finset.univ (fun i _ => a i) = a := by
    ext i
    simp
  rw [he]

/-- Hall pairing with a Schur function is alternating coefficient extraction.
The alphabet must contain all rows of the shape; the other argument is arbitrary. -/
theorem hall_schur_eq_alternating_coeff {d N : ℕ} (ξ : Nat.Partition d)
    (hN : length ξ ≤ N) (f : SymmetricFunction R) :
    hall (schur ξ) f =
      (staircaseAlternant N * alphabetSpecialization R (Fin N) f).coeff (shiftedRows ξ N) := by
  classical
  have hs : schur (R := R) ξ = ∑ σ : Equiv.Perm (Fin N), (Equiv.Perm.sign σ : ℤ) •
      ∏ i : Fin N, completeInt ((rowLength ξ i : ℤ) - (i : ℤ) + (σ i : ℤ)) := by
    rw [← det_jacobiTrudiMatrix ξ hN, ← Matrix.det_transpose, Matrix.det_apply]
    rfl
  have hv : staircaseAlternant (R := R) N = ∑ σ : Equiv.Perm (Fin N),
      (Equiv.Perm.sign σ : ℤ) • ∏ i : Fin N, MvPolynomial.X i ^ (N - 1 - (σ i).val) := by
    rw [staircaseAlternant, Matrix.det_apply]
    rfl
  rw [hs, hv]
  simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply,
    Finset.sum_mul, smul_mul_assoc, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul]
  apply Finset.sum_congr rfl
  intro σ _
  apply congrArg ((Equiv.Perm.sign σ : ℤ) • ·)
  let b : Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => N - 1 - (σ i).val)
  have hm : (∏ i : Fin N, MvPolynomial.X (R := R) i ^ (N - 1 - (σ i).val)) =
      MvPolynomial.monomial b 1 := prod_X_pow_eq_monomial_all b
  rw [hm, ← hall_completeInt_product]
  congr 2
  apply Finset.prod_congr rfl
  intro i _
  apply congrArg (completeInt (R := R))
  have hi := i.isLt
  have hs := (σ i).isLt
  change (rowLength ξ i : ℤ) - (i : ℤ) + (σ i : ℤ) =
    ((rowLength ξ i + (N - 1 - i.val) : ℕ) : ℤ) - ((N - 1 - (σ i).val : ℕ) : ℤ)
  omega

open Classical in
/-- At a strictly decreasing exponent, an alternant has its diagonal coefficient only. -/
theorem coeff_alternantMatrix {N : ℕ} (a b : Fin N →₀ ℕ)
    (ha : StrictAnti a) (hb : StrictAnti b) :
    (alternantMatrix (R := R) b).det.coeff a = if a = b then 1 else 0 := by
  classical
  rw [Matrix.det_apply, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_smul]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin N))]
  · simp only [map_one, one_smul, Equiv.Perm.one_apply, alternantMatrix]
    rw [prod_X_pow_eq_monomial_all, MvPolynomial.coeff_monomial]
    simp only [eq_comm]
  · intro σ _ hσ
    have hn : a ≠ Finsupp.indicator Finset.univ (fun i _ => b (σ i)) := by
      intro he
      apply hσ
      apply perm_eq_one_of_strictAnti ha hb σ
      intro i
      have hv := DFunLike.congr_fun he i
      simpa using hv.symm
    change Equiv.Perm.sign σ • (∏ i : Fin N, MvPolynomial.X (R := R) i ^ b (σ i)).coeff a = 0
    rw [MvPolynomial.coeff_prod_X_pow, ite_eq_right hn, smul_zero]
  · simp

open Classical in
/-- The finite alternant coefficient distinguishes sized partition shapes. -/
theorem coeff_partitionAlternant (ξ μ : Σ d, Nat.Partition d) {N : ℕ}
    (hξ : length ξ.2 ≤ N) (hμ : length μ.2 ≤ N) :
    (partitionAlternant (R := R) μ.2 N).coeff (shiftedRows ξ.2 N) =
      if ξ = μ then 1 else 0 := by
  change (alternantMatrix (R := R) (shiftedRows μ.2 N)).det.coeff (shiftedRows ξ.2 N) = _
  rw [coeff_alternantMatrix _ _ (shiftedRows_strictAnti ξ.2) (shiftedRows_strictAnti μ.2)]
  simp only [shiftedRows_eq_iff ξ μ hξ hμ]

end SymmetricFunction
