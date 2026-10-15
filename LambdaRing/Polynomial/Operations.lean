import LambdaRing.Defs
import LambdaRing.Polynomial.SeriesUnits

/-! # Integral exterior powers on polynomial rings

The total exterior power is a finite product of units with signed exponents.
Only the pre-lambda structure is established here; specialness is a later theorem.
-/

noncomputable section

namespace LambdaRing.Polynomial

open MvPolynomial

variable {σ : Type*}

/-- The finite product encoding exterior powers, including negative coefficients. -/
def totalUnit (f : MvPolynomial σ ℤ) : (PowerSeries (MvPolynomial σ ℤ))ˣ :=
  f.coeff.prod fun m a => lineUnit (monomial m (1 : ℤ)) ^ a

/-- The kth exterior power of an integer polynomial. -/
def operation (k : ℕ) (f : MvPolynomial σ ℤ) : MvPolynomial σ ℤ :=
  PowerSeries.coeff k (totalUnit f : PowerSeries (MvPolynomial σ ℤ))

@[simp] theorem totalUnit_zero : totalUnit (0 : MvPolynomial σ ℤ) = 1 := by
  simp [totalUnit]

theorem totalUnit_add (f g : MvPolynomial σ ℤ) :
    totalUnit (f + g) = totalUnit f * totalUnit g := by
  exact Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ => zpow_add _)

@[simp] theorem totalUnit_monomial (m : σ →₀ ℕ) (a : ℤ) :
    totalUnit (monomial m a) = lineUnit (monomial m (1 : ℤ)) ^ a := by
  exact Finsupp.prod_single_index (zpow_zero _)

/-- Additive polynomial structure becomes multiplication of series units. -/
def totalUnitHom : MvPolynomial σ ℤ →+ Additive ((PowerSeries (MvPolynomial σ ℤ))ˣ) where
  toFun f := Additive.ofMul (totalUnit f)
  map_zero' := totalUnit_zero
  map_add' := totalUnit_add

@[simp] theorem totalUnit_neg (f : MvPolynomial σ ℤ) : totalUnit (-f) = (totalUnit f)⁻¹ :=
  map_neg totalUnitHom f

@[simp] theorem totalUnit_sub (f g : MvPolynomial σ ℤ) :
    totalUnit (f - g) = totalUnit f / totalUnit g := map_sub totalUnitHom f g

theorem constantCoeff_totalUnit (f : MvPolynomial σ ℤ) :
    PowerSeries.constantCoeff (totalUnit f : PowerSeries (MvPolynomial σ ℤ)) = 1 := by
  classical
  simp only [totalUnit, Finsupp.prod, Units.coe_prod, map_prod]
  apply Finset.prod_eq_one
  intro m hm
  exact constantCoeff_unit_zpow _ (constantCoeff_lineUnit _) _

@[simp] theorem operation_zero (f : MvPolynomial σ ℤ) : operation 0 f = 1 := by
  simpa only [operation, PowerSeries.coeff_zero_eq_constantCoeff] using constantCoeff_totalUnit f

theorem operation_add (k : ℕ) (f g : MvPolynomial σ ℤ) : operation k (f + g) =
    ∑ ij ∈ Finset.antidiagonal k, operation ij.1 f * operation ij.2 g := by
  simp only [operation, totalUnit_add, Units.val_mul, PowerSeries.coeff_mul]

theorem operation_one_add (f g : MvPolynomial σ ℤ) :
    operation 1 (f + g) = operation 1 f + operation 1 g := by
  simp [operation, totalUnit_add, PowerSeries.coeff_one_mul, constantCoeff_totalUnit]

@[simp] theorem operation_one_monomial (m : σ →₀ ℕ) (a : ℤ) :
    operation 1 (monomial m a) = monomial m a := by
  rw [operation, totalUnit_monomial, coeff_one_unit_zpow _ (constantCoeff_lineUnit _),
    coeff_one_lineUnit, ← map_zsmul]
  simp

@[simp] theorem operation_one (f : MvPolynomial σ ℤ) : operation 1 f = f := by
  induction f using MvPolynomial.induction_on' with
  | monomial m a => exact operation_one_monomial m a
  | add f g hf hg => rw [operation_one_add, hf, hg]

/-- The integral polynomial pre-lambda structure. No special identity is asserted. -/
instance : PreLambdaRing (MvPolynomial σ ℤ) where
  lambdaOp := operation
  lambda_zero := operation_zero
  lambda_one := operation_one
  lambda_add := operation_add

@[simp] theorem lambda_eq_operation (k : ℕ) (f : MvPolynomial σ ℤ) :
    LambdaRing.lambda k f = operation k f := rfl

/-- Every integer scalar multiplicity becomes a signed unit power. -/
theorem totalUnit_zsmul (z : ℤ) (f : MvPolynomial σ ℤ) :
    totalUnit (z • f) = totalUnit f ^ z := map_zsmul totalUnitHom z f

@[simp] theorem totalUnit_one : totalUnit (1 : MvPolynomial σ ℤ) = lineUnit 1 := by
  rw [MvPolynomial.one_def, totalUnit_monomial, zpow_one, ← MvPolynomial.one_def]

/-- Exterior powers of the multiplicative unit have the exterior-power normalization. -/
@[simp] theorem operation_unit (k : ℕ) : operation k (1 : MvPolynomial σ ℤ) =
    if k ≤ 1 then 1 else 0 := by
  rw [operation, totalUnit_one, coe_lineUnit]
  cases k with
  | zero => simp
  | succ k => cases k <;> simp [PowerSeries.coeff_one, PowerSeries.coeff_X]

/-- A monomial with coefficient -1 has all alternating powers as exterior powers. -/
theorem operation_monomial_neg_one (k : ℕ) (m : σ →₀ ℕ) :
    operation k (monomial m (-1 : ℤ)) = (-monomial m (1 : ℤ)) ^ k := by
  simp [operation, totalUnit_monomial]

/-- Explicit formula for every strictly negative integer coefficient. -/
theorem operation_monomial_negSucc (k r : ℕ) (m : σ →₀ ℕ) :
    operation k (monomial m (-((r+1 : ℕ) : ℤ))) =
      (-monomial m (1 : ℤ)) ^ k * (Nat.choose (r+k) r : MvPolynomial σ ℤ) := by
  rw [operation, totalUnit_monomial, coeff_lineUnit_negSucc]

/-- Coefficient form of the total exterior-power inverse law. -/
theorem operation_neg_convolution (k : ℕ) (f : MvPolynomial σ ℤ) :
    (∑ ij ∈ Finset.antidiagonal k, operation ij.1 f * operation ij.2 (-f)) =
      if k = 0 then 1 else 0 := LambdaRing.lambda_neg_convolution k f

example (m : σ →₀ ℕ) : operation 2 (monomial m (-1 : ℤ)) = monomial m 1 ^ 2 := by
  rw [operation_monomial_neg_one, neg_sq]

example : operation 2 (1 : MvPolynomial σ ℤ) = 0 := by simp

end LambdaRing.Polynomial
