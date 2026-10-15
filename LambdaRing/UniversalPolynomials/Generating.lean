import LambdaRing.UniversalPolynomials.Finite
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

/-! # Finite elementary generating series, before any lambda structure -/

namespace LambdaRing.UniversalPolynomial

noncomputable section

open Finset

variable {σ A : Type*} [Fintype σ] [CommRing A]

/-- The finite product of linear factors belonging to an alphabet. -/
def elementarySeries (x : σ → A) : PowerSeries A :=
  ∏ i, (1 + PowerSeries.C (x i) * PowerSeries.X)

@[simp] theorem coeff_elementarySeries (x : σ → A) (n : ℕ) :
    PowerSeries.coeff n (elementarySeries x) = elementaryValue x n := by
  classical
  have he (i : σ) : 1 + PowerSeries.C (x i) * PowerSeries.X =
      1 + PowerSeries.monomial 1 (x i) := by
    congr 1
    ext k
    by_cases hk : k = 1 <;>
      simp [PowerSeries.coeff_monomial, PowerSeries.coeff_C_mul, PowerSeries.coeff_X, hk]
  simp_rw [elementarySeries, he]
  rw [Finset.prod_one_add, map_sum]
  simp_rw [PowerSeries.prod_monomial, Finset.sum_const, smul_eq_mul, mul_one,
    PowerSeries.coeff_monomial]
  rw [← Finset.sum_filter]
  have hf : (univ : Finset σ).powerset.filter (fun t => n = t.card) = univ.powersetCard n := by
    ext t
    simp [eq_comm]
  rw [hf]
  rfl

end

end LambdaRing.UniversalPolynomial
