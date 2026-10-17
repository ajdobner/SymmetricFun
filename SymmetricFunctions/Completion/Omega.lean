import SymmetricFunctions.Completion.Realization

/-! # Completed complete and elementary series

Uppercase Omega is the complete series in the degree completion. Its inverse
has signed elementary components. Neither construction substitutes into an
uncertified infinite sum.
-/
noncomputable section
namespace SymmetricFunction
open SymmetricFunctions SymmetricFunctions.Series
variable {R : Type*} [CommRing R]
attribute [local irreducible] SymmetricFunction

/-- The completed series with degree-n component h_n, traditionally denoted Ω. -/
def completeSeries : DegreeCompletion R := fun n => ⟨h n, isHomogeneous_h n⟩

/-- The completed elementary series with degree-n component e_n. -/
def elementarySeries : DegreeCompletion R := fun n => ⟨e n, isHomogeneous_e n⟩

/-- The signed elementary series, inverse to the completed complete series. -/
def signedElementarySeries : DegreeCompletion R :=
  fun n => ⟨(-1 : R) ^ n • e n, (isHomogeneous_e n).smul _⟩

/-- The complete series with a sign in each odd degree. -/
def signedCompleteSeries : DegreeCompletion R :=
  fun n => ⟨(-1 : R) ^ n • h n, (isHomogeneous_h n).smul _⟩

@[simp] theorem component_completeSeries (n : ℕ) :
    DegreeCompletion.component R completeSeries n = h n := rfl

@[simp] theorem component_elementarySeries (n : ℕ) :
    DegreeCompletion.component R elementarySeries n = e n := rfl

@[simp] theorem component_signedElementarySeries (n : ℕ) :
    DegreeCompletion.component R signedElementarySeries n = (-1 : R) ^ n • e n := rfl

@[simp] theorem component_signedCompleteSeries (n : ℕ) :
    DegreeCompletion.component R signedCompleteSeries n = (-1 : R) ^ n • h n := rfl

/-- The completed identity E(-u)H(u)=1, interpreted degree by degree. -/
@[simp] theorem signedElementarySeries_mul_completeSeries :
    (signedElementarySeries : DegreeCompletion R) * completeSeries = 1 := by
  apply DegreeCompletion.ext
  intro n
  simpa only [DegreeCompletion.component_mul, component_signedElementarySeries,
    component_completeSeries, smul_mul_assoc, DegreeCompletion.component_one] using
    e_h_convolution (R := R) n

@[simp] theorem completeSeries_mul_signedElementarySeries :
    (completeSeries : DegreeCompletion R) * signedElementarySeries = 1 := by
  rw [mul_comm, signedElementarySeries_mul_completeSeries]

/-- The other signed generating identity E(u)H(-u)=1. -/
@[simp] theorem elementarySeries_mul_signedCompleteSeries :
    (elementarySeries : DegreeCompletion R) * signedCompleteSeries = 1 := by
  apply DegreeCompletion.ext
  intro n
  simpa only [DegreeCompletion.component_mul, component_elementarySeries,
    component_signedCompleteSeries, mul_smul_comm, DegreeCompletion.component_one] using
    e_h_convolution_signed (R := R) n

@[simp] theorem signedCompleteSeries_mul_elementarySeries :
    (signedCompleteSeries : DegreeCompletion R) * elementarySeries = 1 := by
  rw [mul_comm, elementarySeries_mul_signedCompleteSeries]

/-- Ω as an explicit unit, with its signed elementary inverse. -/
def completeSeriesUnit : (DegreeCompletion R)ˣ where
  val := completeSeries
  inv := signedElementarySeries
  val_inv := completeSeries_mul_signedElementarySeries
  inv_val := signedElementarySeries_mul_completeSeries

@[simp] theorem coe_completeSeriesUnit :
    (↑(completeSeriesUnit (R := R)) : DegreeCompletion R) = completeSeries := rfl

@[simp] theorem coe_completeSeriesUnit_inv :
    (↑((completeSeriesUnit (R := R))⁻¹) : DegreeCompletion R) = signedElementarySeries := rfl

variable (R)

/-- Restriction preserves total-degree projections of actual alphabet series. -/
theorem finiteRestriction_homogeneousComponent (N n : ℕ) (F : MvPowerSeries ℕ R) :
    finiteRestriction R N (MvPowerSeries.homogeneousComponent n F) =
      MvPowerSeries.homogeneousComponent n (finiteRestriction R N F) := by
  apply MvPowerSeries.ext
  intro a
  rw [coeff_finiteRestriction, MvPowerSeries.coeff_homogeneousComponent,
    MvPowerSeries.coeff_homogeneousComponent, coeff_finiteRestriction]
  have hd : (a.embDomain Fin.valEmbedding).degree = a.degree :=
    congrArg Multiset.sum (exponentParts_embDomain Fin.valEmbedding a)
  rw [hd]

/-- Finite specialization commutes with each completed homogeneous component. -/
theorem homogeneousComponent_completedFiniteSpecialization (N n : ℕ) (F : DegreeCompletion R) :
    MvPowerSeries.homogeneousComponent n (completedFiniteSpecialization R N F) =
      ((rho R N (DegreeCompletion.component R F n)).val : MvPowerSeries (Fin N) R) := by
  change MvPowerSeries.homogeneousComponent n (finiteRestriction R N (completionToSeries R F)) = _
  rw [← finiteRestriction_homogeneousComponent, ← completionToSeries_component,
    finiteRestriction_toSeries]

/-- Ω specializes degree by degree to the usual finite complete polynomials. -/
@[simp] theorem homogeneousComponent_finite_completeSeries (N n : ℕ) :
    MvPowerSeries.homogeneousComponent n (completedFiniteSpecialization R N completeSeries) =
      (MvPolynomial.hsymm (Fin N) R n : MvPowerSeries (Fin N) R) := by
  rw [homogeneousComponent_completedFiniteSpecialization, component_completeSeries, rho_h]

@[simp] theorem homogeneousComponent_finite_elementarySeries (N n : ℕ) :
    MvPowerSeries.homogeneousComponent n (completedFiniteSpecialization R N elementarySeries) =
      (MvPolynomial.esymm (Fin N) R n : MvPowerSeries (Fin N) R) := by
  rw [homogeneousComponent_completedFiniteSpecialization, component_elementarySeries, rho_e]

/-- Finite restriction preserves the proved inverse; it is a certified completed operation. -/
@[simp] theorem finite_completeSeries_mul_signedElementarySeries (N : ℕ) :
    completedFiniteSpecialization R N completeSeries *
      completedFiniteSpecialization R N signedElementarySeries = 1 := by
  rw [← map_mul, completeSeries_mul_signedElementarySeries, map_one]

/-- The empty alphabet evaluates Ω to its degree-zero component, one. -/
@[simp] theorem completedFiniteSpecialization_zero_completeSeries :
    completedFiniteSpecialization R 0 completeSeries = 1 := by
  apply MvPowerSeries.ext
  intro a
  have ha : a = 0 := Subsingleton.elim _ _
  subst a
  rw [coeff_completedFiniteSpecialization]
  simp

end SymmetricFunction
