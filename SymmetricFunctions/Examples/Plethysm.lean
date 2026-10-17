import SymmetricFunctions.Plethysm.Alphabets
import SymmetricFunctions.Notation

/-! # Plethysm conventions and tensor alphabet examples -/

noncomputable section

open SymmetricFunction LambdaRing
open scoped SymmetricFunctionNotation TensorProduct

namespace SymmetricFunctions.Examples.Plethysm

attribute [local irreducible] SymmetricFunction

example (f g h : Λ[ℤ]) : f⟦g⟧⟦h⟧ = f⟦g⟦h⟧⟧ := plethysm_assoc f g h
example : (p (R := ℤ) 2)⟦p 3⟧ = p 6 := by rw [plethysm_p_p]; rfl
example : (p (R := ℤ) 2)⟦-e 1⟧ = -p 2 := by simp

-- Signed polynomial coefficients are retained; only actual variables are raised to powers.
example : lambdaEval (MvPolynomial.X () - 1 : MvPolynomial Unit ℤ) (p 2) =
    MvPolynomial.X () ^ 2 - 1 := by
  rw [lambdaEval_p_polynomial]
  simp

example (k n : ℕ+) (f : Λ[ℤ]) : adams k (adams n f) = adams (k*n) f :=
  adams_adams k n f

example (f : Λ[ℤ]) : λ[0] (f ⊗ₜ[ℤ] (1 : Λ[ℤ])) = 1 := by simp
example (n : ℕ) : λ[n] ((e (R := ℤ) 1) ⊗ₜ[ℤ] (1 : Λ[ℤ])) = e n ⊗ₜ[ℤ] 1 := by simp

-- The degree-two cross term comes from addition of independent alphabets.
example : λ[2] (e (R := ℤ) 1 ⊗ₜ[ℤ] 1 + 1 ⊗ₜ[ℤ] e (R := ℤ) 1) =
    e 2 ⊗ₜ[ℤ] 1 + e 1 ⊗ₜ[ℤ] e 1 + 1 ⊗ₜ[ℤ] e 2 := by
  simp [lambda_add, Finset.Nat.sum_antidiagonal_succ, add_comm, add_left_comm, add_assoc]

example (f g : Λ[ℤ]) : comultiplication (f⟦g⟧) = lambdaEval (comultiplication g) f :=
  comultiplication_plethysm f g

-- Empty finite alphabets remain valid specialization targets of all tensor operations.
example (n : ℕ) (x : Λ[ℤ] ⊗[ℤ] Λ[ℤ]) :
    tensorAlphabetSpecialization ℤ (Fin 0) (Fin 0) (λ[n] x) =
      λ[n] (tensorAlphabetSpecialization ℤ (Fin 0) (Fin 0) x) :=
  tensorAlphabetSpecialization_lambda n 0 0 x

end SymmetricFunctions.Examples.Plethysm
