import SymmetricFunctions.Notation
import SymmetricFunctions.Examples.Torsion

/-! # Scoped notation: precedence, inference, and mathematical conventions -/

noncomputable section

open SymmetricFunction
open scoped SymmetricFunctionNotation

namespace SymmetricFunctions.Examples.Notation

attribute [local irreducible] SymmetricFunction

section Coefficients

variable {R : Type*} [CommRing R] (f g : Λ[R])

example : ω (ω f) = f := omega_omega f
example : ω (elementary (R := R) 2) = complete 2 := omega_e 2
example : powerSum (R := R) 2 = elementary 1 ^ 2 - 2 * elementary 2 := p_two
example : elementaryCompleteInvolution f = ω f := rfl

-- Unary notation binds more tightly than addition, multiplication, and powers.
example : ω f + g = omega f + g := rfl
example : ω f * g = omega f * g := rfl
example : ω f^2 = (omega f)^2 := rfl

end Coefficients

section ExteriorPowers

variable {A : Type*} [CommRing A] [PreLambdaRing A] (a b : A) (n m : ℕ)

example : λ[0] a = 1 := LambdaRing.lambda_zero a
example : λ[n + 1] a = LambdaRing.lambda (n + 1) a := rfl
example : λ[n] a + b = LambdaRing.lambda n a + b := rfl
example : λ[n] a^2 = (LambdaRing.lambda n a)^2 := rfl
example : λ[n] (a + b) = LambdaRing.lambda n (a + b) := rfl
example : λ[n] λ[m] a = LambdaRing.lambda n (LambdaRing.lambda m a) := rfl

end ExteriorPowers

section Plethysm

variable (f g k : Λ[ℤ]) (n : ℕ)

example : f⟦g⟧ = lambdaEval g f := rfl
example : (f + g)⟦k⟧ = f⟦k⟧ + g⟦k⟧ := add_plethysm f g k
example : f + g⟦k⟧ = f + plethysm g k := rfl
example : f * g⟦k⟧ = f * plethysm g k := rfl
example : f⟦g⟧^2 = (plethysm f g)^2 := rfl
example : f⟦g⟧⟦k⟧ = plethysm (plethysm f g) k := rfl
example : f⟦g⟦k⟧⟧ = plethysm f (plethysm g k) := rfl
example : (f⟦g⟧)⟦k⟧ = f⟦g⟦k⟧⟧ := plethysm_assoc f g k
example : ω f⟦g⟧ = omega (plethysm f g) := rfl
example : (ω f)⟦g⟧ = plethysm (omega f) g := rfl
example : λ[n] f⟦g⟧ = LambdaRing.lambda n (plethysm f g) := rfl
example : (λ[n] f)⟦g⟧ = λ[n] (f⟦g⟧) := lambda_plethysm n f g
example : (elementary n)⟦g⟧ = λ[n] g := plethysm_e n g
example : f⟦elementary 1⟧ = f := plethysm_e_one f

end Plethysm

section ParameterConvention

open MvPolynomial LambdaRing.Polynomial

-- In the one-letter alphabet t, p₂[t] = t². Here t is a polynomial variable.
private theorem powerSum_two_at_variable :
    lambdaEval (X () : MvPolynomial Unit ℤ) (p 2) = X () ^ 2 := by
  rw [p_two, map_sub, map_pow, map_mul, map_ofNat, lambdaEval_e, lambdaEval_e,
    LambdaRing.lambda_one]
  have h : λ[2] (X () : MvPolynomial Unit ℤ) = 0 := by
    change operation 2 (X ()) = 0
    simp [X, operation, coe_lineUnit]
  rw [h, mul_zero, sub_zero]

-- In the virtual negative alphabet -1, p₂[-1] = -1.
private theorem powerSum_two_at_negative_one :
    lambdaEval (-1 : MvPolynomial Unit ℤ) (p 2) = -1 := by
  rw [p_two, map_sub, map_pow, map_mul, map_ofNat, lambdaEval_e, lambdaEval_e,
    LambdaRing.lambda_one]
  have h : λ[2] (-1 : MvPolynomial Unit ℤ) = 1 := by
    change operation 2 (-1) = 1
    simp [operation, coe_lineUnit_inv]
  rw [h]
  ring

-- Specializing t to -1 after computing p₂[t] gives +1, not p₂[-1].
example : MvPolynomial.eval (fun _ : Unit => (-1 : ℤ))
    (lambdaEval (X () : MvPolynomial Unit ℤ) (p 2)) = 1 := by
  rw [powerSum_two_at_variable]
  simp

example : MvPolynomial.eval (fun _ : Unit => (-1 : ℤ))
    (lambdaEval (-1 : MvPolynomial Unit ℤ) (p 2)) = -1 := by
  rw [powerSum_two_at_negative_one]
  simp

end ParameterConvention

-- Exterior-power notation still works in the proved target with additive torsion.
example : λ[2] SymmetricFunction.Examples.Torsion.epsilon = 0 := by
  rw [← SymmetricFunction.Examples.Torsion.evaluation_e_two]
  exact (lambdaEval_e _ 2).symm

end SymmetricFunctions.Examples.Notation
