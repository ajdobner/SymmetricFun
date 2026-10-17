import SymmetricFunctions.Schur.SkewDeterminant
import SymmetricFunctions.Partition.HorizontalStrip

/-! # The existing skew determinant in one letter -/
noncomputable section
open scoped BigOperators

namespace SymmetricFunctions
variable {R : Type*} [CommRing R]

/-- One-variable exponent vectors are determined by their total degree. -/
theorem finOne_exponent (a : Fin 1 →₀ ℕ) : a = Finsupp.single 0 a.degree := by
  have hd : a.degree = a 0 := by rw [Finsupp.degree_eq_sum]; simp
  apply Finsupp.ext
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [hd]

/-- Homogeneity recovers a one-variable polynomial from its value at one. -/
theorem homogeneous_finOne (f : MvPolynomial (Fin 1) R) {n : ℕ}
    (hf : f.IsHomogeneous n) :
    f = MvPolynomial.monomial (Finsupp.single 0 n) (MvPolynomial.eval (fun _ => 1) f) := by
  have he : f = MvPolynomial.monomial (Finsupp.single 0 n)
      (f.coeff (Finsupp.single 0 n)) := by
    apply MvPolynomial.eq_monomial_of_support_subset_singleton
    intro a ha
    have hd : a.degree = n := (hf.degree_eq_sum_deg_support ha).symm
    rw [finOne_exponent a, hd]
  have hv := congrArg (MvPolynomial.eval (fun _ : Fin 1 => (1 : R))) he
  simp only [MvPolynomial.eval_monomial, one_pow, Finsupp.prod,
    Finset.prod_const_one, mul_one] at hv
  rw [hv]
  exact he

open Classical in
/-- The finite complete polynomial in one variable is the corresponding power. -/
theorem hsymm_finOne [DecidableEq (Fin 1)] (n : ℕ) :
    MvPolynomial.hsymm (Fin 1) R n = MvPolynomial.X (0 : Fin 1) ^ n := by
  apply MvPolynomial.ext
  intro a
  have he : MvPolynomial.hsymm (Fin 1) R n =
      @MvPolynomial.hsymm (Fin 1) R _ _ (fun a b => Classical.propDecidable (a = b)) n :=
    congrArg (fun dec : DecidableEq (Fin 1) => @MvPolynomial.hsymm (Fin 1) R _ _ dec n)
      (Subsingleton.elim _ _)
  rw [he, coeff_hsymm, MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial]
  have hh : Finsupp.single (0 : Fin 1) n = a ↔ a.degree = n := by
    constructor
    · intro ha
      rw [← ha, Finsupp.degree_single]
    · intro ha
      rw [finOne_exponent a, ha]
  simp only [hh]


end SymmetricFunctions

namespace SymmetricFunction
open SymmetricFunctions SymmetricFunctions.Partition
variable {R : Type*} [CommRing R]

/-- Specialize in one actual letter, then set that letter to one. This map is bounded. -/
def oneLetterEvaluation (R : Type*) [CommRing R] : SymmetricFunction R →ₐ[R] R :=
  (MvPolynomial.aeval (fun _ : Fin 1 => (1 : R))).comp (alphabetSpecialization R (Fin 1))

@[simp] theorem oneLetterEvaluation_h (n : ℕ) : oneLetterEvaluation R (h n) = 1 := by
  classical
  simp [oneLetterEvaluation, hsymm_finOne]

@[simp] theorem oneLetterEvaluation_completeInt (k : ℤ) :
    oneLetterEvaluation R (completeInt k) = if 0 ≤ k then 1 else 0 := by
  unfold completeInt
  split_ifs <;> simp

/-- The threshold matrix is the actual image of the skew Jacobi–Trudi matrix. -/
def skewThresholdMatrix {d e : ℕ} (ξ : Nat.Partition d) (μ : Nat.Partition e) (L : ℕ) :
    Matrix (Fin L) (Fin L) R := fun i j =>
  if (rowLength μ j : ℤ) - (j : ℤ) ≤ (rowLength ξ i : ℤ) - (i : ℤ) then 1 else 0

theorem oneLetterEvaluation_skewJacobiTrudiMatrix {d e : ℕ} (ξ : Nat.Partition d)
    (μ : Nat.Partition e) (L : ℕ) :
    (skewJacobiTrudiMatrix (R := R) ξ μ L).map (oneLetterEvaluation R) =
      skewThresholdMatrix ξ μ L := by
  ext i j
  simp only [Matrix.map_apply, skewJacobiTrudiMatrix, oneLetterEvaluation_completeInt,
    skewThresholdMatrix]
  congr 1
  apply propext
  omega
/-- Horizontal strips give an upper triangular threshold matrix with diagonal one. -/
theorem det_skewThresholdMatrix_of_horizontalStrip {d e : ℕ} {ξ : Nat.Partition d}
    {μ : Nat.Partition e} (hs : HorizontalStrip μ ξ) (L : ℕ) :
    (skewThresholdMatrix (R := R) ξ μ L).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · have hd (i : Fin L) : (rowLength μ i : ℤ) - (i : ℤ) ≤
        (rowLength ξ i : ℤ) - (i : ℤ) := by
      have := (contained_iff_rowLength μ ξ).mp hs.1 i
      omega
    simp [skewThresholdMatrix, hd]
  · intro i j hji
    have hi : j.val + 1 ≤ i.val := by exact Nat.succ_le_of_lt hji
    have hrow := rowLength_antitone ξ hi
    have hh := hs.2 j
    have hneg : ¬ (rowLength μ j : ℤ) - (j : ℤ) ≤
        (rowLength ξ i : ℤ) - (i : ℤ) := by omega
    simp only [skewThresholdMatrix, ite_eq_right hneg]

/-- The first failed interlacing inequality makes two adjacent threshold rows equal. -/
theorem det_skewThresholdMatrix_eq_zero_of_not_horizontalStrip {d e L : ℕ}
    {ξ : Nat.Partition d} {μ : Nat.Partition e} (hξ : length ξ ≤ L)
    (hc : Contained μ ξ) (hs : ¬ HorizontalStrip μ ξ) :
    (skewThresholdMatrix (R := R) ξ μ L).det = 0 := by
  classical
  have hex : ∃ i, rowLength μ i < rowLength ξ (i + 1) := by
    by_contra hh
    apply hs
    exact ⟨hc, fun i => Nat.le_of_not_gt (fun hi => hh ⟨i, hi⟩)⟩
  let k := Nat.find hex
  have hk : rowLength μ k < rowLength ξ (k + 1) := Nat.find_spec hex
  have hkm : ∀ i < k, rowLength ξ (i + 1) ≤ rowLength μ i :=
    fun i hi => Nat.le_of_not_gt (Nat.find_min hex hi)
  have hkl : k + 1 < L := lt_of_lt_of_le
    ((rowLength_pos_iff ξ (k + 1)).mp (lt_of_le_of_lt (Nat.zero_le _) hk)) hξ
  let i : Fin L := ⟨k, by omega⟩
  let i' : Fin L := ⟨k + 1, hkl⟩
  apply Matrix.det_zero_of_row_eq (i := i) (j := i') (by
    intro he
    have := congrArg Fin.val he
    dsimp [i, i'] at this
    omega)
  funext j
  have hξrow : rowLength ξ (k + 1) ≤ rowLength ξ k :=
    rowLength_antitone ξ (Nat.le_succ k)
  by_cases hj : j.val < k
  · have hfirst := hkm j hj
    have hrow := rowLength_antitone ξ (Nat.succ_le_of_lt hj)
    change rowLength ξ k ≤ rowLength ξ (j.val + 1) at hrow
    have h0 : ¬ (rowLength μ j : ℤ) - (j : ℤ) ≤
        (rowLength ξ i : ℤ) - (i : ℤ) := by
      change ¬ (rowLength μ j : ℤ) - (j : ℤ) ≤ (rowLength ξ k : ℤ) - (k : ℤ)
      omega
    have h1 : ¬ (rowLength μ j : ℤ) - (j : ℤ) ≤
        (rowLength ξ i' : ℤ) - (i' : ℤ) := by
      change ¬ (rowLength μ j : ℤ) - (j : ℤ) ≤
        (rowLength ξ (k + 1) : ℤ) - ((k + 1 : ℕ) : ℤ)
      omega
    simp only [skewThresholdMatrix, ite_eq_right h0, ite_eq_right h1]
  · have hm := rowLength_antitone μ (Nat.le_of_not_gt hj)
    have h0 : (rowLength μ j : ℤ) - (j : ℤ) ≤
        (rowLength ξ i : ℤ) - (i : ℤ) := by
      change (rowLength μ j : ℤ) - (j : ℤ) ≤ (rowLength ξ k : ℤ) - (k : ℤ)
      omega
    have h1 : (rowLength μ j : ℤ) - (j : ℤ) ≤
        (rowLength ξ i' : ℤ) - (i' : ℤ) := by
      change (rowLength μ j : ℤ) - (j : ℤ) ≤
        (rowLength ξ (k + 1) : ℤ) - ((k + 1 : ℕ) : ℤ)
      omega
    simp only [skewThresholdMatrix, ite_eq_left h0, ite_eq_left h1]

open Classical in
/-- Scalar one-letter evaluation detects horizontal strips integrally. -/
theorem oneLetterEvaluation_skewSchur {d e : ℕ} (ξ : Nat.Partition d) (μ : Nat.Partition e) :
    oneLetterEvaluation R (skewSchur ξ μ) = if HorizontalStrip μ ξ then 1 else 0 := by
  classical
  by_cases hc : Contained μ ξ
  · let L := max (length ξ) (length μ)
    have hξ : length ξ ≤ L := le_max_left _ _
    have hμ : length μ ≤ L := le_max_right _ _
    rw [← skew_jacobiTrudi ξ μ hξ hμ]
    have hm := (oneLetterEvaluation R).map_det (skewJacobiTrudiMatrix ξ μ L)
    change oneLetterEvaluation R (skewJacobiTrudiMatrix ξ μ L).det =
      ((skewJacobiTrudiMatrix ξ μ L).map (oneLetterEvaluation R)).det at hm
    rw [hm, oneLetterEvaluation_skewJacobiTrudiMatrix]
    by_cases hs : HorizontalStrip μ ξ
    · simp only [ite_eq_left hs, det_skewThresholdMatrix_of_horizontalStrip hs]
    · simp only [ite_eq_right hs,
        det_skewThresholdMatrix_eq_zero_of_not_horizontalStrip hξ hc hs]
  · rw [skewSchur_eq_zero_of_not_contained ξ μ hc, map_zero,
      ite_eq_right (fun h => hc h.1)]

open Classical in
/-- The actual skew Schur function in one letter is a horizontal-strip monomial. -/
theorem alphabetSpecialization_one_skewSchur {d e : ℕ} (ξ : Nat.Partition d)
    (μ : Nat.Partition e) :
    alphabetSpecialization R (Fin 1) (skewSchur ξ μ) =
      if HorizontalStrip μ ξ then MvPolynomial.X (0 : Fin 1) ^ (d - e) else 0 := by
  classical
  have hh : (alphabetSpecialization R (Fin 1) (skewSchur ξ μ)).IsHomogeneous (d - e) := by
    rw [alphabetSpecialization_fin]
    exact isHomogeneous_rho R 1 (d - e) _ (isHomogeneous_skewSchur ξ μ)
  rw [homogeneous_finOne _ hh]
  change MvPolynomial.monomial (Finsupp.single 0 (d - e))
    (oneLetterEvaluation R (skewSchur ξ μ)) = _
  rw [oneLetterEvaluation_skewSchur]
  split_ifs <;> simp [MvPolynomial.X_pow_eq_monomial]

end SymmetricFunction
