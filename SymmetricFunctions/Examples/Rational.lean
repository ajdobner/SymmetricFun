import SymmetricFunctions.Alphabets
import SymmetricFunctions.Basis.PowerSum
import SymmetricFunctions.Notation
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # Rational evaluation conventions

These examples distinguish coefficients in the outer function, parameters in
an inner alphabet, and virtual signs. Rational-function denominators are checked
before using the X/(1-t) evaluator. No completed-series notation is introduced.
-/

noncomputable section

namespace SymmetricFunction.Examples

open SymmetricFunctions SymmetricFunction
open scoped TensorProduct SymmetricFunctionNotation

attribute [local irreducible] SymmetricFunction

variable {R : Type*} [CommRing R] [Algebra ℚ R]

-- Polynomial freeness and the basis include degree zero and repeated parts.
example (k : ℕ+) : powerSumPolynomialEquiv R (MvPolynomial.X k) = p k := by simp

example : pBasisAll R ⟨0, default⟩ = 1 := by simp

example : pBasisAll R ⟨4, Partition.union (Nat.Partition.indiscrete 2)
    (Nat.Partition.indiscrete 2)⟩ = p 2 * p 2 := by
  rw [pBasisAll_apply, ← powerSumChangeOfGenerators_ePart, ← ePart_mul, map_mul]
  have he : ePart (R := R) (Nat.Partition.indiscrete 2) = e 2 := by simp [ePart]
  rw [he]
  exact congrArg (fun x => x * x) (powerSumChangeOfGenerators_e (R := R) 2)

-- The zero coefficient ring is not excluded by the presentation or basis.
example : Module.Basis (Nat.Partition 3) PUnit (homogeneousSubmodule PUnit 3) := pBasis PUnit 3

-- Virtual negation negates every p_k, including even indices.
example (k : ℕ+) : negativeAlphabetEval (p (R := R)) (p (R := R) k) = -p k := by simp

example : negativeAlphabetEval (p (R := R)) (p (R := R) 2) = -p 2 := by simp

-- Specializing a formal scaling parameter to -1 is different.
example : scaledAlphabetEval (-1) (p (R := R)) (p (R := R) 2) = p 2 := by norm_num

-- An outer coefficient t stays fixed; t inside the alphabet receives its kth power.
example (t : R) :
    scaledAlphabetEval (algebraMap R (Λ[R]) t) p
        (algebraMap R (Λ[R]) t * p 2) =
      algebraMap R (Λ[R]) t ^ 3 * p 2 := by
  rw [map_mul, AlgHom.commutes, scaledAlphabetEval_p]
  norm_num
  ring

-- Distinct tensor blocks retain independent power-sum assignments.
example {A : Type*} [CommRing A] [Algebra R A] (x y : ℕ+ → A) :
    tensorAlphabetEval x y (p (R := R) 2 ⊗ₜ[R] p 3) = x 2 * y 3 := by simp

-- A polynomial parameter inside the inner argument transforms under Adams.
example (k : ℕ+) :
    mixedPlethysticEval (MvPolynomial.X () ⊗ₜ[ℚ] p (R := ℚ) 1) (p k) =
      (MvPolynomial.X () ^ (k : ℕ)) ⊗ₜ[ℚ] p k := by simp

example : mixedPlethysticEval
    (-((MvPolynomial.X () : MvPolynomial Unit ℚ) ⊗ₜ[ℚ] p (R := ℚ) 1)) (p 2) =
      -((MvPolynomial.X () ^ 2) ⊗ₜ[ℚ] p (R := ℚ) 2) := by simp

-- This also works with no polynomial parameters.
example {A : Type*} [CommRing A] [Algebra R A] (x : ℕ+ → A) (k : ℕ+) :
    mixedAlphabetEval (R := R) (fun i : Fin 0 => Fin.elim0 i) x
      ((1 : MvPolynomial (Fin 0) R) ⊗ₜ[R] p k) = x k := by simp

/-- In a rational-function field every required geometric denominator is nonzero. -/
theorem ratFuncGeometricDenominators (k : ℕ+) :
    IsUnit (1 - (RatFunc.X : RatFunc ℚ) ^ (k : ℕ)) := by
  apply isUnit_iff_ne_zero.mpr
  rw [← RatFunc.algebraMap_X, ← map_pow, ← map_one (algebraMap (Polynomial ℚ) (RatFunc ℚ)),
    ← map_sub]
  apply RatFunc.algebraMap_ne_zero
  intro h
  have hc := congrArg (fun q : Polynomial ℚ => q.coeff 0) h
  simp [k.ne_zero.symm] at hc

-- Genuine X/(1-t) evaluation in a field of rational functions.
example (x : ℕ+ → RatFunc ℚ) (k : ℕ+) :
    geometricAlphabetEval (R := ℚ) RatFunc.X ratFuncGeometricDenominators x (p k) *
      (1 - RatFunc.X ^ (k : ℕ)) = x k :=
  geometricAlphabetEval_denominator _ _ _ _

example (x : ℕ+ → RatFunc ℚ) (k : ℕ+) :
    geometricAlphabetEval (R := ℚ) RatFunc.X ratFuncGeometricDenominators x (p k) =
      x k / (1 - RatFunc.X ^ (k : ℕ)) :=
  geometricAlphabetEval_p_field _ _ _ _

end SymmetricFunction.Examples
