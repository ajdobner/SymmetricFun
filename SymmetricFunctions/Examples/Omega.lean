import SymmetricFunctions.Notation

/-! Completed Omega, its inverse, scope and degree conventions. -/
noncomputable section
namespace SymmetricFunction.Examples
open scoped SymmetricFunctionNotation
variable {R : Type*} [CommRing R]

example : DegreeCompletion.component R Ω 0 = 1 := by simp
example : DegreeCompletion.component R Ω 1 = h 1 := by simp
example : DegreeCompletion.component R Ω 2 = h 2 := by simp
example : DegreeCompletion.component R Ω 3 = h 3 := by simp

example : DegreeCompletion.component R signedElementarySeries 1 = -e 1 := by simp
example : DegreeCompletion.component R signedElementarySeries 2 = e 2 := by simp
example : (Ω : DegreeCompletion R) * signedElementarySeries = 1 := by simp
example : signedElementarySeries * (Ω : DegreeCompletion R) = 1 := by simp

example : (Ω : DegreeCompletion (ZMod 2)) * signedElementarySeries = 1 := by simp
example : (Ω : DegreeCompletion PUnit) * signedElementarySeries = 1 := by simp

example : DegreeCompletion.truncate R 2 Ω = 1 + h 1 + h 2 := by
  simp [DegreeCompletion.truncate, Finset.sum_range_succ]

example (N : ℕ) :
    MvPowerSeries.homogeneousComponent 2 (completedFiniteSpecialization R N Ω) =
      (MvPolynomial.hsymm (Fin N) R 2 : MvPowerSeries (Fin N) R) := by simp

example : completedFiniteSpecialization R 0 Ω = 1 := by simp

example (N : ℕ) : completedFiniteSpecialization R N Ω *
    completedFiniteSpecialization R N signedElementarySeries = 1 := by simp

-- Lowercase omega continues to act on bounded functions.
example : ω (e (R := R) 2) = DegreeCompletion.component R Ω 2 := by simp

end SymmetricFunction.Examples
