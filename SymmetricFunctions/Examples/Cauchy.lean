import SymmetricFunctions.Cauchy
import SymmetricFunctions.Notation
import Mathlib.Data.ZMod.Basic

/-! # Completed Cauchy conventions and low components -/
noncomputable section
namespace SymmetricFunction.Examples
open SymmetricFunctions
open scoped TensorProduct SymmetricFunctionNotation
variable {R : Type*} [CommRing R]

example : CompletedTensor.component R (cauchyKernel R) 0 = 1 := by simp
example : CompletedTensor.component R (cauchyKernel R) 1 = 0 := by simp
example : CompletedTensor.component R (cauchyKernel R) 2 = e 1 ⊗ₜ[R] e 1 := by simp
example : CompletedTensor.component R (cauchyKernel R) 5 = 0 := component_cauchyKernel_odd 2

-- The two degree-four expansions agree without division by any integer.
example : (∑ μ : Nat.Partition 2, schur (R := ZMod 6) μ ⊗ₜ[ZMod 6] schur (R := ZMod 6) μ) =
    ∑ μ : Nat.Partition 2, hPart (R := ZMod 6) μ ⊗ₜ[ZMod 6] mPart (R := ZMod 6) μ :=
  cauchySchurComponent_eq_completeMonomial 2

example : cauchyKernel PUnit = 0 := by
  apply GradedCompletion.ext
  intro n
  apply tensorHall_schur_ext
  intro ξ μ
  exact Subsingleton.elim _ _

example : completedTensorSpecialization (ZMod 6) 2 3 (cauchyKernel (ZMod 6)) =
    finiteCauchyProduct (Fin 2) (Fin 3) (ZMod 6) :=
  completedTensorSpecialization_cauchyKernel 2 3

-- Ω[X+Y] has a degree-one term; the Cauchy kernel Ω[XY] starts in degree two.
-- The first expression uses the actual completed coproduct, not a product-alphabet notation.
example : CompletedTensor.component R (completedCoproduct R Ω) 1 =
    e 1 ⊗ₜ[R] 1 + 1 ⊗ₜ[R] e 1 := by
  simp [Finset.Nat.sum_antidiagonal_succ, add_comm]

end SymmetricFunction.Examples
