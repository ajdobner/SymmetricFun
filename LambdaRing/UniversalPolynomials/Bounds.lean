import SymmetricFunctions.Finite.StableRange

/-! # Injectivity of elementary substitution with bounded variable indices -/

namespace LambdaRing.UniversalPolynomial

noncomputable section

open SymmetricFunction

variable (R : Type*) [CommRing R]

/-- Agreement of polynomial elementary substitution with the public specialization. -/
theorem elementarySpecialization_eq_rho (N : ℕ) (q : MvPolynomial ℕ+ R) :
    MvPolynomial.aeval (fun i : ℕ+ => MvPolynomial.esymm (Fin N) R i) q =
      (rho R N ((polynomialEquiv R).symm q) : MvPolynomial (Fin N) R) := by
  simp only [rho, eval, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  exact
    Subalgebra.mvPolynomial_aeval_coe (MvPolynomial.symmetricSubalgebra (Fin N) R)
      (fun i : ℕ+ => ⟨MvPolynomial.esymm (Fin N) R i, MvPolynomial.esymm_isSymmetric _ _ _⟩) q

/-- Truncation fixes any expression in the first N generators, without a degree restriction. -/
theorem truncate_of_vars_le (N : ℕ) (q : MvPolynomial ℕ+ R)
    (hq : ∀ i ∈ q.vars, (i : ℕ) ≤ N) :
    truncate R N ((polynomialEquiv R).symm q) = (polynomialEquiv R).symm q := by
  apply MvPolynomial.hom_congr_vars
    (f₁ := (truncate R N).toRingHom.comp (polynomialEquiv R).symm.toRingHom)
    (f₂ := (polynomialEquiv R).symm.toRingHom) (p₁ := q) (p₂ := q)
  · ext r
    change truncate R N ((polynomialEquiv R).symm
      (algebraMap R (MvPolynomial ℕ+ R) r)) =
      (polynomialEquiv R).symm (algebraMap R (MvPolynomial ℕ+ R) r)
    simp only [AlgEquiv.commutes, AlgHom.commutes]
  · intro i hi _
    simp [truncate_e_of_le R (hq i hi)]
  · rfl

/-- Elementary substitution is injective on expressions using only the available indices. -/
theorem elementarySpecialization_injective_of_vars_le (N : ℕ)
    {q r : MvPolynomial ℕ+ R}
    (hq : ∀ i ∈ q.vars, (i : ℕ) ≤ N) (hr : ∀ i ∈ r.vars, (i : ℕ) ≤ N)
    (he : MvPolynomial.aeval (fun i : ℕ+ => MvPolynomial.esymm (Fin N) R i) q =
      MvPolynomial.aeval (fun i : ℕ+ => MvPolynomial.esymm (Fin N) R i) r) : q = r := by
  rw [elementarySpecialization_eq_rho, elementarySpecialization_eq_rho] at he
  have hs := congrArg (liftSymmetric R N) (Subtype.ext he)
  change truncate R N ((polynomialEquiv R).symm q) =
    truncate R N ((polynomialEquiv R).symm r) at hs
  rw [truncate_of_vars_le R N q hq, truncate_of_vars_le R N r hr] at hs
  exact (polynomialEquiv R).symm.injective hs

end

end LambdaRing.UniversalPolynomial
