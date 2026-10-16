import SymmetricFunctions.Completion.Realization

/-! Weighted degree, convolution, and inclusive truncation examples. -/
noncomputable section
namespace SymmetricFunction.Examples
open DegreeCompletion
variable {R : Type*} [CommRing R]

example : Function.Injective (completionEmbedding (ZMod 2)) :=
  completionEmbedding_injective _

example : Function.Injective (completionEmbedding PUnit) :=
  completionEmbedding_injective _

example : component R (completionEmbedding R (e 3)) 3 = e 3 := by
  rw [component_completionEmbedding, homogeneousComponent_of_mem (isHomogeneous_e 3)]

example : component R (completionEmbedding R (e 3)) 1 = 0 := by
  rw [component_completionEmbedding, homogeneousComponent_of_mem_ne (isHomogeneous_e 3) (by decide)]

example (F G : DegreeCompletion R) :
    component R (F * G) 0 = component R F 0 * component R G 0 := by
  simp [component_mul]

example (F : DegreeCompletion R) : DegreeCompletion.truncate R 0 F = component R F 0 := by
  simp [DegreeCompletion.truncate]

example (D : ℕ) (F G : DegreeCompletion R) :
    DegreeCompletion.truncate R D (F * G) = DegreeCompletion.truncate R D
      (completionEmbedding R (DegreeCompletion.truncate R D F * DegreeCompletion.truncate R D G)) :=
  DegreeCompletion.truncate_mul R D F G

example : DegreeCompletion (ZMod 2) ≃ₐ[ZMod 2]
    SymmetricFunctions.Series.SymmetricSeries (ZMod 2) := completionSeriesEquiv _

example (F : DegreeCompletion R) (n : ℕ) :
    toSeries R (component R F n) =
      MvPowerSeries.homogeneousComponent n (completionToSeries R F) :=
  completionToSeries_component R F n

example (N : ℕ) (f : SymmetricFunction R) :
    completedFiniteSpecialization R N (completionEmbedding R f) =
      ((rho R N f).val : MvPowerSeries (Fin N) R) := by simp

example : DegreeCompletion PUnit ≃ₐ[PUnit]
    SymmetricFunctions.Series.SymmetricSeries PUnit := completionSeriesEquiv _

end SymmetricFunction.Examples
