import SymmetricFunctions.Completion.Omega
import Mathlib.RingTheory.MvPowerSeries.Substitution

/-! # Certified substitution into completed symmetric functions

Infinite alphabets require coefficientwise finiteness as well as positive order
(or the more general nilpotent-constant condition in HasSubst). No map in this
module exposes Mathlib's dummy substitution outside its proved hypotheses.
-/
noncomputable section
namespace SymmetricFunction
open SymmetricFunctions.Series
variable {R τ : Type*} [CommRing R]
attribute [local irreducible] SymmetricFunction

/-- Positive alphabet letters with coefficientwise finite support admit substitution. -/
theorem hasSubst_of_positive_locallyFinite (a : ℕ → MvPowerSeries τ R)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hfinite : ∀ d, {i | MvPowerSeries.coeff d (a i) ≠ 0}.Finite) :
    MvPowerSeries.HasSubst a where
  const_coeff i := by rw [h0 i]; exact IsNilpotent.zero
  coeff_zero := hfinite

/-- Increasing positive powers form a valid infinite alphabet, finite at each coefficient. -/
theorem hasSubst_positivePowers (s : τ) :
    MvPowerSeries.HasSubst (fun n : ℕ => (MvPowerSeries.X s : MvPowerSeries τ R) ^ (n + 1)) := by
  classical
  apply hasSubst_of_positive_locallyFinite
  · intro n
    simp
  · intro d
    apply (Set.finite_Iic d.degree).subset
    intro n hn
    change n ≤ d.degree
    change MvPowerSeries.coeff d ((MvPowerSeries.X s : MvPowerSeries τ R) ^ (n + 1)) ≠ 0 at hn
    rw [MvPowerSeries.coeff_X_pow] at hn
    split_ifs at hn with hd
    · have he := congrArg Finsupp.degree hd
      simp only [Finsupp.degree_single] at he
      omega
    · exact (hn rfl).elim

/-- Certified substitution in the actual countable alphabet, fixing outer R-coefficients. -/
def completedSubstitution (a : ℕ → MvPowerSeries τ R) (ha : MvPowerSeries.HasSubst a) :
    DegreeCompletion R →ₐ[R] MvPowerSeries τ R :=
  (MvPowerSeries.substAlgHom ha).comp (completionToSeries R)

theorem completedSubstitution_apply (a : ℕ → MvPowerSeries τ R)
    (ha : MvPowerSeries.HasSubst a) (F : DegreeCompletion R) :
    completedSubstitution a ha F = MvPowerSeries.subst a (completionToSeries R F) :=
  MvPowerSeries.substAlgHom_apply ha _

/-- Only finitely many exponent terms contribute to any specified output coefficient. -/
theorem completedSubstitution_coefficient_finite (a : ℕ → MvPowerSeries τ R)
    (ha : MvPowerSeries.HasSubst a) (F : DegreeCompletion R) (b : τ →₀ ℕ) :
    (fun d => MvPowerSeries.coeff d (completionToSeries R F) •
      MvPowerSeries.coeff b (d.prod (fun i n => a i ^ n))).HasFiniteSupport :=
  MvPowerSeries.coeff_subst_finite ha _ b

/-- The output coefficient is a justified finite-support sum, not an unrestricted series sum. -/
theorem coeff_completedSubstitution (a : ℕ → MvPowerSeries τ R)
    (ha : MvPowerSeries.HasSubst a) (F : DegreeCompletion R) (b : τ →₀ ℕ) :
    MvPowerSeries.coeff b (completedSubstitution a ha F) =
      ∑ᶠ d, MvPowerSeries.coeff d (completionToSeries R F) •
        MvPowerSeries.coeff b (d.prod (fun i n => a i ^ n)) := by
  rw [completedSubstitution_apply, MvPowerSeries.coeff_subst ha]

/-- On bounded inputs the certified map is the existing evaluator at its elementary images. -/
theorem completedSubstitution_embedding (a : ℕ → MvPowerSeries τ R)
    (ha : MvPowerSeries.HasSubst a) (f : SymmetricFunction R) :
    completedSubstitution a ha (completionEmbedding R f) =
      eval (fun n : ℕ+ => MvPowerSeries.substAlgHom ha (toSeries R (e n))) f := by
  have he : (completedSubstitution a ha).comp (completionEmbedding R) =
      eval (fun n : ℕ+ => MvPowerSeries.substAlgHom ha (toSeries R (e n))) := by
    apply algHom_ext
    intro n
    simp only [AlgHom.comp_apply, eval_e, completedSubstitution,
      completionToSeries_embedding]
  exact AlgHom.congr_fun he f

/-- Substituting the actual alphabet variables is the completed series realization. -/
@[simp] theorem completedSubstitution_X (F : DegreeCompletion R) :
    completedSubstitution MvPowerSeries.X MvPowerSeries.HasSubst.X F =
      completionToSeries R F := by
  rw [completedSubstitution_apply, MvPowerSeries.subst_self]
  rfl

/-- Evaluation in finitely many positive-degree letters; finiteness of the family is automatic. -/
def completedFiniteEval {N : ℕ} (a : Fin N → MvPowerSeries τ R)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    DegreeCompletion R →ₐ[R] MvPowerSeries τ R :=
  (MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero h0)).comp
    (completedFiniteSpecialization R N)

theorem completedFiniteEval_apply {N : ℕ} (a : Fin N → MvPowerSeries τ R)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (F : DegreeCompletion R) :
    completedFiniteEval a h0 F = MvPowerSeries.subst a (completedFiniteSpecialization R N F) :=
  MvPowerSeries.substAlgHom_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero h0) _

/-- The completed finite evaluator restricts to ordinary polynomial evaluation. -/
@[simp] theorem completedFiniteEval_embedding {N : ℕ} (a : Fin N → MvPowerSeries τ R)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (f : SymmetricFunction R) :
    completedFiniteEval a h0 (completionEmbedding R f) =
      MvPolynomial.aeval a (rho R N f).val := by
  change MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero h0)
    (completedFiniteSpecialization R N (completionEmbedding R f)) = _
  rw [completedFiniteSpecialization_embedding, MvPowerSeries.substAlgHom_coe]

/-- The same bounded agreement stated using the public elementary-generator evaluator. -/
theorem completedFiniteEval_embedding_eq_eval {N : ℕ} (a : Fin N → MvPowerSeries τ R)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (f : SymmetricFunction R) :
    completedFiniteEval a h0 (completionEmbedding R f) =
      eval (fun n : ℕ+ => MvPolynomial.aeval a (MvPolynomial.esymm (Fin N) R n)) f := by
  have he : (completedFiniteEval a h0).comp (completionEmbedding R) =
      eval (fun n : ℕ+ => MvPolynomial.aeval a (MvPolynomial.esymm (Fin N) R n)) := by
    apply algHom_ext
    intro n
    simp only [AlgHom.comp_apply, completedFiniteEval_embedding, eval_e, rho_e]
  exact AlgHom.congr_fun he f

/-- Positive identity letters recover finite alphabet restriction. -/
@[simp] theorem completedFiniteEval_X (N : ℕ) (F : DegreeCompletion R) :
    completedFiniteEval (MvPowerSeries.X : Fin N → MvPowerSeries (Fin N) R)
      (fun _ => MvPowerSeries.constantCoeff_X _) F = completedFiniteSpecialization R N F := by
  rw [completedFiniteEval_apply, MvPowerSeries.subst_self]
  rfl

/-- Every certified evaluation preserves the explicit inverse of Ω. -/
theorem completedSubstitution_complete_mul_inverse (a : ℕ → MvPowerSeries τ R)
    (ha : MvPowerSeries.HasSubst a) :
    completedSubstitution a ha completeSeries *
      completedSubstitution a ha signedElementarySeries = 1 := by
  rw [← map_mul, completeSeries_mul_signedElementarySeries, map_one]

/-- The finite positive-alphabet evaluator also preserves Ω's inverse. -/
theorem completedFiniteEval_complete_mul_inverse {N : ℕ} (a : Fin N → MvPowerSeries τ R)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    completedFiniteEval a h0 completeSeries *
      completedFiniteEval a h0 signedElementarySeries = 1 := by
  rw [← map_mul, completeSeries_mul_signedElementarySeries, map_one]

/-- Completed truncation becomes the finite sum of actual alphabet homogeneous layers. -/
theorem completionToSeries_truncate (D : ℕ) (F : DegreeCompletion R) :
    completionToSeries R (completionEmbedding R (DegreeCompletion.truncate R D F)) =
      ∑ n ∈ Finset.range (D + 1),
        MvPowerSeries.homogeneousComponent n (completionToSeries R F) := by
  rw [completionToSeries_embedding, DegreeCompletion.truncate, map_sum]
  simp only [completionToSeries_component]

/-- Positive substitution is filtered: degrees through D depend only on input degrees through D. -/
theorem truncTotal_completedSubstitution [Finite τ] (a : ℕ → MvPowerSeries τ R)
    (ha : MvPowerSeries.HasSubst a)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (D : ℕ) (F : DegreeCompletion R) :
    MvPowerSeries.truncTotal (D + 1) (completedSubstitution a ha F) =
      MvPowerSeries.truncTotal (D + 1)
        (completedSubstitution a ha (completionEmbedding R (DegreeCompletion.truncate R D F))) := by
  rw [completedSubstitution_apply, completedSubstitution_apply, completionToSeries_truncate]
  exact MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_sum ha h0

/-- The same filtered compatibility for finitely many positive source letters. -/
theorem truncTotal_completedFiniteEval [Finite τ] {N : ℕ} (a : Fin N → MvPowerSeries τ R)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (D : ℕ) (F : DegreeCompletion R) :
    MvPowerSeries.truncTotal (D + 1) (completedFiniteEval a h0 F) =
      MvPowerSeries.truncTotal (D + 1)
        (completedFiniteEval a h0 (completionEmbedding R (DegreeCompletion.truncate R D F))) := by
  have ht : completedFiniteSpecialization R N
      (completionEmbedding R (DegreeCompletion.truncate R D F)) =
      ∑ n ∈ Finset.range (D + 1),
        MvPowerSeries.homogeneousComponent n (completedFiniteSpecialization R N F) := by
    simp only [completedFiniteSpecialization, AlgHom.comp_apply, completionToSeries_truncate,
      map_sum, finiteRestriction_homogeneousComponent]
  rw [completedFiniteEval_apply, completedFiniteEval_apply, ht]
  exact MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_sum
    (MvPowerSeries.hasSubst_of_constantCoeff_zero h0) h0

/-- The finite signed elementary series has no components above the alphabet size. -/
theorem finite_signedElementarySeries_truncate (N : ℕ) :
    completedFiniteSpecialization R N signedElementarySeries =
      completedFiniteSpecialization R N
        (completionEmbedding R (DegreeCompletion.truncate R N signedElementarySeries)) := by
  have he (n : ℕ) :
      MvPowerSeries.homogeneousComponent n
        (completedFiniteSpecialization R N signedElementarySeries) =
      MvPowerSeries.homogeneousComponent n (completedFiniteSpecialization R N
        (completionEmbedding R (DegreeCompletion.truncate R N signedElementarySeries))) := by
    rw [homogeneousComponent_completedFiniteSpecialization,
      homogeneousComponent_completedFiniteSpecialization, component_completionEmbedding,
      DegreeCompletion.homogeneousComponent_truncate]
    by_cases hn : n ≤ N
    · rw [ite_eq_left hn]
    · rw [ite_eq_right hn, component_signedElementarySeries, map_smul,
        rho_e_eq_zero R (Nat.lt_of_not_ge hn), smul_zero, map_zero]
  apply MvPowerSeries.ext
  intro a
  simpa only [MvPowerSeries.coeff_homogeneousComponent, ite_true] using
    congrArg (MvPowerSeries.coeff a) (he a.degree)

/-- One actual alphabet letter turns the signed elementary series into 1-X. -/
theorem finite_signedElementarySeries_one :
    completedFiniteSpecialization R 1 signedElementarySeries =
      1 - MvPowerSeries.X (0 : Fin 1) := by
  have ht : DegreeCompletion.truncate R 1 signedElementarySeries = 1 - e 1 := by
    simp [DegreeCompletion.truncate, Finset.sum_range_succ, sub_eq_add_neg]
  rw [finite_signedElementarySeries_truncate, ht, completedFiniteSpecialization_embedding]
  simp only [map_sub, map_one, Subalgebra.coe_sub, Subalgebra.coe_one, rho_e,
    MvPolynomial.esymm_one, Fin.sum_univ_one]
  change (MvPolynomial.coeToMvPowerSeries.ringHom :
    MvPolynomial (Fin 1) R →+* MvPowerSeries (Fin 1) R) (1 - MvPolynomial.X 0) = _
  rw [map_sub, map_one]
  simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_X]

/-- The one-letter inverse calculation uses a proved zero constant term. -/
@[simp] theorem completedFiniteEval_signedElementary_one (a : MvPowerSeries τ R)
    (h0 : MvPowerSeries.constantCoeff a = 0) :
    completedFiniteEval (fun _ : Fin 1 => a) (fun _ => h0) signedElementarySeries = 1 - a := by
  change MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => h0))
    (completedFiniteSpecialization R 1 signedElementarySeries) = _
  rw [finite_signedElementarySeries_one, map_sub, map_one, MvPowerSeries.substAlgHom_X]

/-- Ω in one positive-degree letter is the geometric inverse of 1-a. -/
theorem completedFiniteEval_complete_one_mul (a : MvPowerSeries τ R)
    (h0 : MvPowerSeries.constantCoeff a = 0) :
    completedFiniteEval (fun _ : Fin 1 => a) (fun _ => h0) completeSeries * (1 - a) = 1 := by
  simpa only [completedFiniteEval_signedElementary_one] using
    completedFiniteEval_complete_mul_inverse (fun _ : Fin 1 => a) (fun _ => h0)

end SymmetricFunction
