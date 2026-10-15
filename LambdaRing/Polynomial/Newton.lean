import LambdaRing.Polynomial.Operations
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.MvPolynomial.Expand

/-! # Integral Newton identities from the constructed total exterior-power series -/

noncomputable section

namespace LambdaRing.Polynomial

open MvPolynomial

variable {A : Type*} [CommRing A]

/-- Logarithmic differentiation of a formal-series unit uses its actual unit inverse. -/
def logDerivative (u : (PowerSeries A)ˣ) : PowerSeries A :=
  PowerSeries.derivative (u : PowerSeries A) * (↑u⁻¹ : PowerSeries A)

@[simp] theorem logDerivative_one : logDerivative (1 : (PowerSeries A)ˣ) = 0 := by
  simp [logDerivative]

theorem logDerivative_mul (u v : (PowerSeries A)ˣ) :
    logDerivative (u * v) = logDerivative u + logDerivative v := by
  simp only [logDerivative, Units.val_mul, mul_inv_rev, Derivation.leibniz, smul_eq_mul]
  calc
    _ = (↑u * (↑u⁻¹ : PowerSeries A)) *
          (PowerSeries.derivative (v : PowerSeries A) * (↑v⁻¹ : PowerSeries A)) +
        (↑v * (↑v⁻¹ : PowerSeries A)) *
          (PowerSeries.derivative (u : PowerSeries A) * (↑u⁻¹ : PowerSeries A)) := by ring
    _ = _ := by simp only [Units.mul_inv, one_mul, add_comm]

/-- Logarithmic differentiation is additive on the multiplicative unit group. -/
def logDerivativeHom : Additive ((PowerSeries A)ˣ) →+ PowerSeries A where
  toFun u := logDerivative u.toMul
  map_zero' := logDerivative_one
  map_add' := logDerivative_mul

@[simp] theorem logDerivative_zpow (u : (PowerSeries A)ˣ) (z : ℤ) :
    logDerivative (u ^ z) = z • logDerivative u := map_zsmul logDerivativeHom z (Additive.ofMul u)

/-- The ghost coefficient of a line unit is its signed ordinary power. -/
theorem coeff_logDerivative_lineUnit (a : A) (n : ℕ) :
    PowerSeries.coeff n (logDerivative (lineUnit a)) = (-1 : A)^n * a^(n+1) := by
  simp only [logDerivative, coe_lineUnit, map_add, PowerSeries.derivative_one,
    Derivation.leibniz, PowerSeries.derivative_C, PowerSeries.derivative_X,
    smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
  rw [PowerSeries.coeff_C_mul, coeff_lineUnit_inv]
  rw [neg_pow, pow_succ]
  ring

variable {σ : Type*}

/-- Additive logarithmic derivative of the actual total exterior-power construction. -/
def logTotalHom : MvPolynomial σ ℤ →+ PowerSeries (MvPolynomial σ ℤ) :=
  logDerivativeHom.comp totalUnitHom

/-- The signed ghost coefficients are exactly the monomial Adams substitutions. -/
theorem coeff_logDerivative_totalUnit (f : MvPolynomial σ ℤ) (n : ℕ) :
    PowerSeries.coeff n (logDerivative (totalUnit f)) =
      (-1 : ℤ)^n • expand (n+1) f := by
  induction f using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [totalUnit_monomial, logDerivative_zpow, map_zsmul, coeff_logDerivative_lineUnit,
      monomial_pow, one_pow, expand_monomial]
    rw [← mul_smul_comm, ← map_zsmul]
    simp [zsmul_eq_mul]
  | add f g hf hg =>
    rw [totalUnit_add, logDerivative_mul, map_add, hf, hg, map_add, smul_add]

/-- The undivided integral Newton recurrence, valid for every signed polynomial. -/
theorem operation_newton (f : MvPolynomial σ ℤ) (n : ℕ) :
    (n+1 : ℤ) • operation (n+1) f =
      ∑ ij ∈ Finset.antidiagonal n,
        (-1 : ℤ)^ij.1 • (operation ij.2 f * expand (ij.1+1) f) := by
  have h : PowerSeries.derivative (totalUnit f : PowerSeries (MvPolynomial σ ℤ)) =
      logDerivative (totalUnit f) * (totalUnit f : PowerSeries (MvPolynomial σ ℤ)) := by
    rw [logDerivative, mul_assoc, Units.inv_mul, mul_one]
  have hc := congrArg (PowerSeries.coeff n) h
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at hc
  simp only [coeff_logDerivative_totalUnit] at hc
  change operation (n+1) f * ((n : MvPolynomial σ ℤ) + 1) = _ at hc
  rw [show (n+1 : ℤ) • operation (n+1) f = operation (n+1) f * ((n : MvPolynomial σ ℤ) + 1) by
    simp [zsmul_eq_mul, mul_comm]]
  rw [hc]
  apply Finset.sum_congr rfl
  intro ij hij
  change ((-1 : ℤ)^ij.1 • expand (ij.1+1) f) * operation ij.2 f = _
  rw [smul_mul_assoc, mul_comm]

end LambdaRing.Polynomial
