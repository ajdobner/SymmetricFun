import SymmetricFunctions.Examples.Foundation
import SymmetricFunctions.Hopf
import SymmetricFunctions.Lambda.Universal
import SymmetricFunctions.Examples.Torsion

/-! # Initial core release convention examples

These checks exercise the public API with its foundational representation sealed.
-/

noncomputable section

namespace SymmetricFunctions.Examples

open SymmetricFunction
open scoped TensorProduct

attribute [local irreducible] SymmetricFunction

variable {R : Type*} [CommRing R]

example : e (R := R) 0 = 1 := e_zero

example (n : ℕ+) : rho R 0 (e (n : ℕ)) = 0 := rho_e_eq_zero R n.pos

example : h (R := R) 2 = e 1 ^ 2 - e 2 := h_two

example : p (R := R) 2 = e 1 ^ 2 - 2 * e 2 := p_two

example : comultiplication (e (R := R) 2) =
    1 ⊗ₜ[R] e 2 + e 1 ⊗ₜ[R] e 1 + e 2 ⊗ₜ[R] 1 := by
  simp [Finset.Nat.sum_antidiagonal_succ, add_assoc]

example : antipode (e (R := R) 2) = h 2 := by simp

example (n : ℕ) : LambdaRing.lambda n (e (R := ℤ) 1) = e n := lambda_e_one n

example {A : Type*} [CommRing A] [PreLambdaRing A] [SpecialLambdaRing A]
    (a : A) (n : ℕ) : lambdaEval a (e n) = LambdaRing.lambda n a := lambdaEval_e a n

example : SymmetricFunction.Examples.Torsion.evaluation (e 1) ≠ 0 := by
  rw [SymmetricFunction.Examples.Torsion.evaluation_e_one]
  exact SymmetricFunction.Examples.Torsion.epsilon_ne_zero

example : (2 : ℤ) • SymmetricFunction.Examples.Torsion.evaluation (e 1) = 0 := by
  rw [SymmetricFunction.Examples.Torsion.evaluation_e_one]
  exact SymmetricFunction.Examples.Torsion.two_smul_epsilon

end SymmetricFunctions.Examples
