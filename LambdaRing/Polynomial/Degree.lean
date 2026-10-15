import LambdaRing.Polynomial.Operations
import Mathlib.Algebra.MvPolynomial.Degrees

/-! # Uniform polynomial degree bounds for exterior powers -/

noncomputable section

namespace LambdaRing.Polynomial

open MvPolynomial

variable {σ : Type*}

/-- The kth coefficient has degree at most k*d, uniformly over all k. -/
def CoefficientBound (d : ℕ) (f : PowerSeries (MvPolynomial σ ℤ)) : Prop :=
  ∀ k, (PowerSeries.coeff k f).totalDegree ≤ k * d

theorem coefficientBound_one (d : ℕ) : CoefficientBound (σ := σ) d 1 := by
  intro k
  simp only [PowerSeries.coeff_one]
  split <;> simp

theorem CoefficientBound.mul {d : ℕ} {f g : PowerSeries (MvPolynomial σ ℤ)}
    (hf : CoefficientBound d f) (hg : CoefficientBound d g) : CoefficientBound d (f * g) := by
  intro k
  rw [PowerSeries.coeff_mul]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun ij hij => ?_)
  calc
    _ ≤ (PowerSeries.coeff ij.1 f).totalDegree + (PowerSeries.coeff ij.2 g).totalDegree :=
      totalDegree_mul _ _
    _ ≤ ij.1 * d + ij.2 * d := add_le_add (hf ij.1) (hg ij.2)
    _ = k * d := by rw [← add_mul, Finset.mem_antidiagonal.mp hij]

theorem CoefficientBound.pow {d : ℕ} {f : PowerSeries (MvPolynomial σ ℤ)}
    (hf : CoefficientBound d f) (n : ℕ) : CoefficientBound d (f ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using coefficientBound_one (σ := σ) d
  | succ n ih => rw [pow_succ]; exact ih.mul hf

theorem coefficientBound_prod {ι : Type*} (d : ℕ) (s : Finset ι)
    (f : ι → PowerSeries (MvPolynomial σ ℤ)) (hf : ∀ i ∈ s, CoefficientBound d (f i)) :
    CoefficientBound d (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using coefficientBound_one (σ := σ) d
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem coefficientBound_lineUnit {d : ℕ} {a : MvPolynomial σ ℤ}
    (ha : a.totalDegree ≤ d) :
    CoefficientBound d (lineUnit a : PowerSeries (MvPolynomial σ ℤ)) := by
  intro k
  rw [coe_lineUnit]
  cases k with
  | zero => simp
  | succ k =>
    cases k with
    | zero => simpa using ha
    | succ k => simp [PowerSeries.coeff_one]

theorem coefficientBound_lineUnit_inv {d : ℕ} {a : MvPolynomial σ ℤ}
    (ha : a.totalDegree ≤ d) :
    CoefficientBound d (↑(lineUnit a)⁻¹ : PowerSeries (MvPolynomial σ ℤ)) := by
  intro k
  rw [coeff_lineUnit_inv]
  have hneg : (-a).totalDegree ≤ d := by
    simpa using (totalDegree_smul_le (-1 : ℤ) a).trans ha
  exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left k hneg)

/-- Positive and negative multiplicities obey the same degree bound. -/
theorem coefficientBound_lineUnit_zpow {d : ℕ} {a : MvPolynomial σ ℤ}
    (ha : a.totalDegree ≤ d) (z : ℤ) :
    CoefficientBound d (↑(lineUnit a ^ z) : PowerSeries (MvPolynomial σ ℤ)) := by
  cases z with
  | ofNat n =>
    simpa only [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val] using
      (coefficientBound_lineUnit ha).pow n
  | negSucc n =>
    simpa only [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val] using
      (coefficientBound_lineUnit_inv ha).pow (n+1)

/-- The full total exterior power preserves the uniform coefficient bound. -/
theorem coefficientBound_totalUnit {d : ℕ} {f : MvPolynomial σ ℤ}
    (hf : f.totalDegree ≤ d) :
    CoefficientBound d (totalUnit f : PowerSeries (MvPolynomial σ ℤ)) := by
  classical
  simp only [totalUnit, Finsupp.prod, Units.coe_prod]
  apply coefficientBound_prod
  intro m hm
  apply coefficientBound_lineUnit_zpow
  exact (totalDegree_monomial_le m (1 : ℤ)).trans ((le_totalDegree hm).trans hf)

/-- Exterior power k multiplies a polynomial degree bound by k, even with negative coefficients. -/
theorem operation_totalDegree_le (k d : ℕ) (f : MvPolynomial σ ℤ)
    (hf : f.totalDegree ≤ d) : (operation k f).totalDegree ≤ k * d :=
  coefficientBound_totalUnit hf k

theorem operation_totalDegree (k : ℕ) (f : MvPolynomial σ ℤ) :
    (operation k f).totalDegree ≤ k * f.totalDegree := operation_totalDegree_le k _ f le_rfl

end LambdaRing.Polynomial
