import SymmetricFunctions.Completion
import SymmetricFunctions.Notation

/-! Positive degree, local finiteness, and usable Omega evaluations. -/
noncomputable section
namespace SymmetricFunction.Examples
open scoped SymmetricFunctionNotation
variable {R : Type*} [CommRing R]

example (N : ℕ) :
    completedFiniteEval (MvPowerSeries.X : Fin N → MvPowerSeries (Fin N) R)
      (fun _ => MvPowerSeries.constantCoeff_X _) Ω = completedFiniteSpecialization R N Ω := by
  simp

example : completedFiniteEval (fun _ : Fin 1 => (MvPowerSeries.X (0 : Fin 1) :
    MvPowerSeries (Fin 1) R)) (by simp) Ω * (1 - MvPowerSeries.X 0) = 1 :=
  completedFiniteEval_complete_one_mul _ (by simp)

-- Squared letters have positive degree as well; positivity is proved, not assumed by syntax.
example : completedFiniteEval (fun _ : Fin 1 => (MvPowerSeries.X (0 : Fin 1) :
    MvPowerSeries (Fin 1) (ZMod 2)) ^ 2) (by simp) Ω * (1 - MvPowerSeries.X 0 ^ 2) = 1 :=
  completedFiniteEval_complete_one_mul _ (by simp)

-- A genuinely infinite alphabet is valid when the orders increase.
example : MvPowerSeries.HasSubst (fun n : ℕ =>
    (MvPowerSeries.X (0 : Fin 1) : MvPowerSeries (Fin 1) R) ^ (n + 1)) :=
  hasSubst_positivePowers _

example : completedSubstitution
    (fun n : ℕ => (MvPowerSeries.X (0 : Fin 1) : MvPowerSeries (Fin 1) R) ^ (n + 1))
    (hasSubst_positivePowers _) Ω * completedSubstitution
    (fun n : ℕ => (MvPowerSeries.X (0 : Fin 1) : MvPowerSeries (Fin 1) R) ^ (n + 1))
    (hasSubst_positivePowers _) signedElementarySeries = 1 :=
  completedSubstitution_complete_mul_inverse _ _

-- Positive degree alone fails for infinitely many identical nonzero letters.
example : ¬ MvPowerSeries.HasSubst (fun _ : ℕ =>
    (MvPowerSeries.X (0 : Fin 1) : MvPowerSeries (Fin 1) ℤ)) := by
  intro ha
  have hf := ha.coeff_zero (Finsupp.single 0 1)
  have he : {i : ℕ | MvPowerSeries.coeff (Finsupp.single 0 1)
      (MvPowerSeries.X (0 : Fin 1) : MvPowerSeries (Fin 1) ℤ) ≠ 0} = Set.univ := by
    simp
  rw [he] at hf
  exact Set.infinite_univ hf

example (N D : ℕ) (a : Fin N → MvPowerSeries (Fin 1) R)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    MvPowerSeries.truncTotal (D + 1) (completedFiniteEval a h0 Ω) =
      MvPowerSeries.truncTotal (D + 1)
        (completedFiniteEval a h0 (completionEmbedding R (DegreeCompletion.truncate R D Ω))) :=
  truncTotal_completedFiniteEval a h0 D Ω

example (N : ℕ) (a : Fin N → MvPowerSeries (Fin 1) R)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (f : Λ[R]) :
    completedFiniteEval a h0 (completionEmbedding R f) =
      eval (fun n : ℕ+ => MvPolynomial.aeval a (MvPolynomial.esymm (Fin N) R n)) f :=
  completedFiniteEval_embedding_eq_eval a h0 f

end SymmetricFunction.Examples
