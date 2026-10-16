import SymmetricFunctions.Finite.SeriesAlphabets
import SymmetricFunctions.Finite.CompleteCoefficients
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-! # The finite Cauchy product as a justified formal series

Each denominator has constant coefficient one, hence a genuine inverse over
any commutative coefficient ring. Iterated coefficients give complete products.
-/
noncomputable section
namespace SymmetricFunctions
variable (σ τ R : Type*) [Fintype σ] [Fintype τ] [CommRing R]

/-- The finite product alphabet Cauchy denominator. -/
def finiteCauchyDenominator : MvPowerSeries (σ ⊕ τ) R :=
  ∏ j : τ, ∏ i : σ, (1 - MvPowerSeries.X (Sum.inl i) * MvPowerSeries.X (Sum.inr j))

/-- Every factor is an actual formal inverse with unit constant coefficient. -/
def finiteCauchyProduct : MvPowerSeries (σ ⊕ τ) R :=
  ∏ j : τ, ∏ i : σ,
    MvPowerSeries.invOfUnit (1 - MvPowerSeries.X (Sum.inl i) * MvPowerSeries.X (Sum.inr j)) 1

/-- The specified finite product is inverse to its denominator. -/
theorem finiteCauchyProduct_mul_denominator :
    finiteCauchyProduct σ τ R * finiteCauchyDenominator σ τ R = 1 := by
  classical
  simp only [finiteCauchyProduct, finiteCauchyDenominator, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro j _
  apply Finset.prod_eq_one
  intro i _
  exact MvPowerSeries.invOfUnit_mul _ 1 (by simp)

/-- Complete generating series in each right variable, with polynomial left coefficients. -/
def finiteCauchyColumns : MvPowerSeries τ (MvPolynomial σ R) :=
  ∏ j : τ, PowerSeries.subst (MvPowerSeries.X j) (completeSeries σ R)

open Classical in
/-- Independent right variables read independent complete polynomials. -/
theorem coeff_finiteCauchyColumns (b : τ →₀ ℕ) :
    MvPowerSeries.coeff b (finiteCauchyColumns σ τ R) =
      ∏ j : τ, MvPolynomial.hsymm σ R (b j) := by
  classical
  rw [finiteCauchyColumns, coeff_prod_subst_X]
  simp only [coeff_completeSeries]

/-- The polynomial-coefficient column series has the expected finite denominator. -/
theorem finiteCauchyColumns_mul_denominator :
    finiteCauchyColumns σ τ R *
      (∏ j : τ, ∏ i : σ,
        (1 - MvPowerSeries.C (MvPolynomial.X (R := R) i) * MvPowerSeries.X j)) = 1 := by
  classical
  have he (j : τ) : PowerSeries.subst (MvPowerSeries.X j) (elementarySeries σ R) =
      ∏ i : σ, (1 - MvPowerSeries.C (MvPolynomial.X (R := R) i) * MvPowerSeries.X j) := by
    rw [← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.X j), elementarySeries, map_prod]
    simp only [map_sub, map_one, map_mul, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_C, PowerSeries.subst_X (PowerSeries.HasSubst.X j)]
  simp_rw [finiteCauchyColumns, ← he, ← Finset.prod_mul_distrib,
    ← PowerSeries.subst_mul (PowerSeries.HasSubst.X _), completeSeries_mul_elementarySeries]
  simp only [← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.X _), map_one,
    Finset.prod_const_one]

/-- Joint variables and iterated polynomial coefficients give the same finite Cauchy series. -/
theorem sumSeriesEquiv_finiteCauchyProduct :
    sumSeriesEquiv (finiteCauchyProduct σ τ R) =
      MvPowerSeries.map MvPolynomial.coeToMvPowerSeries.ringHom (finiteCauchyColumns σ τ R) := by
  classical
  let D := sumSeriesEquiv (finiteCauchyDenominator σ τ R)
  have hleft : sumSeriesEquiv (finiteCauchyProduct σ τ R) * D = 1 := by
    rw [← map_mul, finiteCauchyProduct_mul_denominator, map_one]
  have hright : MvPowerSeries.map MvPolynomial.coeToMvPowerSeries.ringHom
      (finiteCauchyColumns σ τ R) * D = 1 := by
    have hh := congrArg (MvPowerSeries.map
      (MvPolynomial.coeToMvPowerSeries.ringHom : MvPolynomial σ R →+* MvPowerSeries σ R))
      (finiteCauchyColumns_mul_denominator σ τ R)
    simpa only [D, finiteCauchyDenominator, map_mul, map_one, map_prod, map_sub,
      MvPowerSeries.map_C, MvPowerSeries.map_X, sumSeriesEquiv_X_inl, sumSeriesEquiv_X_inr,
      MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_X] using hh
  calc
    _ = sumSeriesEquiv (finiteCauchyProduct σ τ R) *
        (D * MvPowerSeries.map MvPolynomial.coeToMvPowerSeries.ringHom
          (finiteCauchyColumns σ τ R)) := by rw [mul_comm D, hright, mul_one]
    _ = _ := by rw [← mul_assoc, hleft, one_mul]

open Classical in
/-- A finite Cauchy coefficient is the coefficient of an actual complete product. -/
theorem coeff_finiteCauchyProduct (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    MvPowerSeries.coeff (a.sumElim b) (finiteCauchyProduct σ τ R) =
      (∏ j : τ, MvPolynomial.hsymm σ R (b j)).coeff a := by
  have he := congrArg (fun F => MvPowerSeries.coeff a (MvPowerSeries.coeff b F))
    (sumSeriesEquiv_finiteCauchyProduct σ τ R)
  change MvPowerSeries.coeff (a.sumElim b) (finiteCauchyProduct σ τ R) = _ at he
  simpa only [MvPowerSeries.coeff_map, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
    MvPolynomial.coeff_coe, coeff_finiteCauchyColumns] using he

/-- Equivalently, finite Cauchy coefficients count nonnegative matrices with both margins. -/
theorem coeff_finiteCauchyProduct_eq_card (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    MvPowerSeries.coeff (a.sumElim b) (finiteCauchyProduct σ τ R) =
      (marginMatrices b a).card := by
  rw [coeff_finiteCauchyProduct, coeff_prod_hsymm]

omit [Fintype τ] in
/-- The two margins of a finite matrix have the same total size. -/
theorem degree_eq_of_mem_marginMatrices [Finite τ] (a : σ →₀ ℕ) (b : τ →₀ ℕ)
    (A : σ →₀ τ →₀ ℕ) (hA : A ∈ marginMatrices a b) : a.degree = b.degree := by
  classical
  let := Fintype.ofFinite τ
  obtain ⟨hc, hr⟩ := (mem_marginMatrices a b A).mp hA
  rw [finsupp_degree_eq_sum, finsupp_degree_eq_sum]
  simp_rw [← hr, ← hc]
  exact Finset.sum_comm

/-- Different degrees in the two alphabets have zero Cauchy coefficient. -/
theorem coeff_finiteCauchyProduct_eq_zero (a : σ →₀ ℕ) (b : τ →₀ ℕ)
    (hab : a.degree ≠ b.degree) :
    MvPowerSeries.coeff (a.sumElim b) (finiteCauchyProduct σ τ R) = 0 := by
  rw [coeff_finiteCauchyProduct_eq_card]
  have he : marginMatrices b a = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro A hA
    exact hab (degree_eq_of_mem_marginMatrices τ σ b a A hA).symm
  rw [he, Finset.card_empty, Nat.cast_zero]

end SymmetricFunctions
