import SymmetricFunctions.Completion.Hopf
import SymmetricFunctions.Notation

/-! Completed alphabet addition and the total tensor degree. -/
noncomputable section
namespace SymmetricFunction.Examples
open scoped TensorProduct SymmetricFunctionNotation
variable {R : Type*} [CommRing R]

example : completedCoproduct R Ω = completedTensorProduct R Ω Ω :=
  completedCoproduct_completeSeries R

example : CompletedTensor.component R (completedCoproduct R Ω) 0 = 1 := by simp

example : CompletedTensor.component R (completedCoproduct R Ω) 2 =
    h 2 ⊗ₜ[R] 1 + h 1 ⊗ₜ[R] h 1 + 1 ⊗ₜ[R] h 2 := by
  simp [Finset.Nat.sum_antidiagonal_succ, add_comm, add_left_comm]

example (f : Λ[R]) : completedCoproduct R (completionEmbedding R f) =
    tensorCompletionMap R (comultiplication f) := completedCoproduct_embedding R f

-- Both tensor degrees are counted: e_2 tensor e_3 appears in total degree five.
example : CompletedTensor.component R (tensorCompletionMap R (e 2 ⊗ₜ[R] e 3)) 5 =
    e 2 ⊗ₜ[R] e 3 := by
  rw [component_tensorCompletionMap_tmul R (isHomogeneous_e 2) (isHomogeneous_e 3)]
  rfl

example : CompletedTensor.component R (tensorCompletionMap R (e 2 ⊗ₜ[R] e 3)) 2 = 0 := by
  rw [component_tensorCompletionMap_tmul R (isHomogeneous_e 2) (isHomogeneous_e 3)]
  rfl

end SymmetricFunction.Examples
