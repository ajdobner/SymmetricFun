import SymmetricFunctions.Completion.Single
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPowerSeries.Trunc

/-! # Coefficientwise realization of a graded completion

A polynomial map preserving alphabet degree extends to formal series: the
coefficient of an exponent reads only the component of that total degree.
-/
noncomputable section
namespace SymmetricFunctions.GradedCompletion
variable {R A σ : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (G : ℕ → Submodule R A) [SetLike.GradedMonoid G]
variable (φ : A →ₐ[R] MvPolynomial σ R)
variable (hφ : ∀ n (a : A), a ∈ G n → (φ a).IsHomogeneous n)

/-- Assemble the image of each component at its matching alphabet degree. -/
def polynomialSeriesFamily (F : GradedCompletion G) : MvPowerSeries σ R :=
  fun a => (φ (component G F a.degree)).coeff a

omit [SetLike.GradedMonoid G] in
@[simp] theorem coeff_polynomialSeriesFamily (F : GradedCompletion G) (a : σ →₀ ℕ) :
    MvPowerSeries.coeff a (polynomialSeriesFamily G φ F) =
      (φ (component G F a.degree)).coeff a := rfl

include hφ in
/-- Two finite antidiagonals suffice: incompatible degree splits have zero coefficients. -/
theorem polynomialSeriesFamily_mul (F H : GradedCompletion G) :
    polynomialSeriesFamily G φ (F * H) =
      polynomialSeriesFamily G φ F * polynomialSeriesFamily G φ H := by
  classical
  apply MvPowerSeries.ext
  intro a
  rw [coeff_polynomialSeriesFamily, component_mul, map_sum, MvPolynomial.coeff_sum,
    MvPowerSeries.coeff_mul]
  simp_rw [map_mul, MvPolynomial.coeff_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro bc hbc
  have hd : bc.1.degree + bc.2.degree = a.degree := by
    rw [← map_add, Finset.mem_antidiagonal.mp hbc]
  rw [Finset.sum_eq_single (bc.1.degree, bc.2.degree)]
  · rfl
  · intro ij _ hij
    by_cases hi : bc.1.degree = ij.1
    · have hj : bc.2.degree ≠ ij.2 := by
        intro hj
        exact hij (Prod.ext hi.symm hj.symm)
      rw [(hφ _ _ (component_mem G H _)).coeff_eq_zero hj, mul_zero]
    · rw [(hφ _ _ (component_mem G F _)).coeff_eq_zero hi, zero_mul]
  · simp [Finset.mem_antidiagonal, hd]

/-- A degree-preserving polynomial algebra map extends to the degree completion. -/
def polynomialRealization : GradedCompletion G →ₐ[R] MvPowerSeries σ R where
  toFun := polynomialSeriesFamily G φ
  map_zero' := by
    ext a
    simp [coeff_polynomialSeriesFamily, component_zero]
  map_one' := by
    classical
    ext a
    rw [coeff_polynomialSeriesFamily, component_one]
    by_cases ha : a = 0
    · subst a; simp
    · have hd : a.degree ≠ 0 := fun he => ha ((Finsupp.degree_eq_zero_iff a).mp he)
      simp [hd, ha, MvPowerSeries.coeff_one]
  map_add' F H := by
    ext a
    simp [coeff_polynomialSeriesFamily, component_add]
  map_mul' := polynomialSeriesFamily_mul G φ hφ
  commutes' r := by
    classical
    ext a
    rw [coeff_polynomialSeriesFamily, component_algebraMap]
    by_cases ha : a = 0
    · subst a; simp [MvPowerSeries.algebraMap_apply]
    · have hd : a.degree ≠ 0 := fun he => ha ((Finsupp.degree_eq_zero_iff a).mp he)
      simp [hd, ha, MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C]

@[simp] theorem coeff_polynomialRealization (F : GradedCompletion G) (a : σ →₀ ℕ) :
    MvPowerSeries.coeff a (polynomialRealization G φ hφ F) =
      (φ (component G F a.degree)).coeff a := rfl

/-- Homogeneous projection recovers the image of the corresponding component. -/
theorem polynomialRealization_component (F : GradedCompletion G) (n : ℕ) :
    ((φ (component G F n)) : MvPowerSeries σ R) =
      MvPowerSeries.homogeneousComponent n (polynomialRealization G φ hφ F) := by
  classical
  apply MvPowerSeries.ext
  intro a
  rw [MvPolynomial.coeff_coe, MvPowerSeries.coeff_homogeneousComponent,
    coeff_polynomialRealization]
  by_cases ha : a.degree = n
  · simp only [ha, ite_true]
  · rw [ite_eq_right ha]
    exact (hφ _ _ (component_mem G F n)).coeff_eq_zero ha

/-- A single homogeneous input specializes to its ordinary polynomial. -/
@[simp] theorem polynomialRealization_single (n : ℕ) (a : A) (ha : a ∈ G n) :
    polynomialRealization G φ hφ (single G n a ha) = (φ a : MvPowerSeries σ R) := by
  classical
  apply MvPowerSeries.ext
  intro b
  rw [coeff_polynomialRealization, component_single, MvPolynomial.coeff_coe]
  split_ifs with hb
  · rfl
  · rw [map_zero]
    exact (hφ n a ha).coeff_eq_zero hb |>.symm

end SymmetricFunctions.GradedCompletion
