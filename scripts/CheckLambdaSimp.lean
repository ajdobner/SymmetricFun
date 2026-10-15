import SymmetricFunctions

/-! Root-import regressions for the public exterior-power simplification API. -/

noncomputable section

open SymmetricFunction LambdaRing

-- The originally reported failure, and its all-index form.
example : lambda 2 (e (R := ℤ) 1) = e 2 := by simp
example (n : ℕ) : lambda n (e (R := ℤ) 1) = e n := by simp
example : lambda 2 (lambda 1 (e (R := ℤ) 1)) = e 2 := by simp
-- The polynomial presentation is an algebra equivalence, not a lambda equivalence.
example : polynomialEquiv ℤ (lambda 2 (e (R := ℤ) 1)) ≠
    lambda 2 (polynomialEquiv ℤ (e 1)) := by simp
example (f : SymmetricFunction ℤ) : lambda 0 f = 1 := by simp
example (n : ℕ) : lambda n (0 : SymmetricFunction ℤ) = if n = 0 then 1 else 0 := by simp
example (n : ℕ) : lambda n (1 : SymmetricFunction ℤ) = if n ≤ 1 then 1 else 0 := by simp
example : lambda 2 (-e (R := ℤ) 1) = h 2 := by simp [h_two]

-- Signed-input simplification uses no characteristic or torsion-free assumption.
example {A : Type*} [CommRing A] [PreLambdaRing A] (a : A) :
    lambda 2 (-a) = a ^ 2 - lambda 2 a := by simp
example : lambda 2 (-SymmetricFunction.Examples.Torsion.epsilon) = 0 := by
  have h := SymmetricFunction.Examples.Torsion.evaluation_e_two
  change lambdaEval SymmetricFunction.Examples.Torsion.epsilon (e 2) = 0 at h
  rw [lambdaEval_e] at h
  simp [h]

-- The polynomial bridge follows the same public normal form.
example {σ : Type*} (i : σ) : lambda 2 (MvPolynomial.X i : MvPolynomial σ ℤ) = 0 := by simp
example {σ : Type*} (n : ℕ) :
    lambda n (0 : MvPolynomial σ ℤ) = if n = 0 then 1 else 0 := by simp
example {σ : Type*} (n : ℕ) :
    lambda n (1 : MvPolynomial σ ℤ) = if n ≤ 1 then 1 else 0 := by simp
example {σ : Type*} (n : ℕ) (m : σ →₀ ℕ) :
    lambda n (MvPolynomial.monomial m (-1 : ℤ)) = (-MvPolynomial.monomial m 1)^n := by simp
example {σ : Type*} (i : σ) :
    lambda 2 (-MvPolynomial.X i : MvPolynomial σ ℤ) = MvPolynomial.X i ^ 2 := by simp

-- Global simp must leave an unreduced public operation public, syntactically.
-- A no-op is intentional in these two normal-form regression checks.
set_option linter.unusedTactic false in
example (n : ℕ) (f z : SymmetricFunction ℤ) (h : lambda n f = z) : lambda n f = z := by
  conv_lhs => simp
  guard_target =ₛ lambda n f = z
  exact h
set_option linter.unusedTactic false in
example {σ : Type*} (n : ℕ) (f z : MvPolynomial σ ℤ) (h : lambda n f = z) :
    lambda n f = z := by
  conv_lhs => simp
  guard_target =ₛ lambda n f = z
  exact h

-- Both old bridge names remain available when implementation access is intentional.
example (n : ℕ) (f : SymmetricFunction ℤ) : lambda n f = lambdaOperation n f :=
  lambda_eq_lambdaOperation n f
example {σ : Type*} (n : ℕ) (f : MvPolynomial σ ℤ) :
    lambda n f = LambdaRing.Polynomial.operation n f :=
  LambdaRing.Polynomial.lambda_eq_operation n f
