import LambdaRing.UniversalPolynomials

/-! # Exterior-power pre-lambda rings and special lambda rings

The operations are specified before specialness. All coefficient rings, including
rings with torsion and the zero ring, are permitted. Universal identities use the
integral polynomials constructed independently in `UniversalPolynomials`.
-/

/-- Exterior-power operations satisfying the additive convolution law. -/
class PreLambdaRing (A : Type*) [CommRing A] where
  lambdaOp : ℕ → A → A
  lambda_zero : ∀ a, lambdaOp 0 a = 1
  lambda_one : ∀ a, lambdaOp 1 a = a
  lambda_add : ∀ n a b, lambdaOp n (a + b) =
    ∑ ij ∈ Finset.antidiagonal n, lambdaOp ij.1 a * lambdaOp ij.2 b

namespace LambdaRing

variable {A : Type*} [CommRing A] [PreLambdaRing A]

/-- The nth exterior-power operation. Its index includes zero. -/
abbrev lambda (n : ℕ) (a : A) : A := PreLambdaRing.lambdaOp n a

@[simp] theorem lambda_zero (a : A) : lambda 0 a = 1 := PreLambdaRing.lambda_zero a
@[simp] theorem lambda_one (a : A) : lambda 1 a = a := PreLambdaRing.lambda_one a

theorem lambda_add (n : ℕ) (a b : A) : lambda n (a + b) =
    ∑ ij ∈ Finset.antidiagonal n, lambda ij.1 a * lambda ij.2 b :=
  PreLambdaRing.lambda_add n a b

@[simp] theorem lambda_zero_input (n : ℕ) : lambda n (0 : A) = if n = 0 then 1 else 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      have hadd := lambda_add (n+1) (0 : A) 0
      rw [zero_add, Finset.Nat.sum_antidiagonal_succ] at hadd
      simp only [lambda_zero, one_mul] at hadd
      have hs : (∑ ij ∈ Finset.antidiagonal n,
          lambda (ij.1+1) (0 : A) * lambda ij.2 0) = lambda (n+1) 0 := by
        rw [Finset.sum_eq_single (n,0)]
        · simp
        · intro ij hij hne
          have hsum := Finset.mem_antidiagonal.mp hij
          have hj : ij.2 ≠ 0 := by
            intro hz
            apply hne
            exact Prod.ext (by omega) hz
          rw [ih ij.2 (by omega), ite_eq_right hj, mul_zero]
        · simp
      rw [hs] at hadd
      have hz : lambda (n+1) (0 : A) = 0 := (add_eq_left.mp hadd.symm)
      simpa using hz

/-- The total exterior powers of an additive inverse multiply to one. -/
theorem lambda_neg_convolution (n : ℕ) (a : A) :
    (∑ ij ∈ Finset.antidiagonal n, lambda ij.1 a * lambda ij.2 (-a)) =
      if n = 0 then 1 else 0 := by
  rw [← lambda_add, add_neg_cancel, lambda_zero_input]

end LambdaRing

/-- Specialness of a pre-lambda structure, using integral universal polynomials.
The iteration law includes the inner index zero; the unit law is explicit. -/
class SpecialLambdaRing (A : Type*) [CommRing A] [PreLambdaRing A] : Prop where
  lambda_unit : ∀ n, LambdaRing.lambda n (1 : A) = if n ≤ 1 then 1 else 0
  lambda_mul : ∀ n (a b : A), LambdaRing.lambda n (a * b) =
    MvPolynomial.aeval (Sum.elim
      (fun i : ℕ+ => LambdaRing.lambda i a) (fun j : ℕ+ => LambdaRing.lambda j b))
      (LambdaRing.UniversalPolynomial.productPolynomial n)
  lambda_iterate : ∀ n m (a : A), LambdaRing.lambda n (LambdaRing.lambda m a) =
    MvPolynomial.aeval (fun i : ℕ+ => LambdaRing.lambda i a)
      (LambdaRing.UniversalPolynomial.iterationPolynomial n m)

namespace LambdaRing

variable {A : Type*} [CommRing A] [PreLambdaRing A] [SpecialLambdaRing A]

@[simp] theorem lambda_unit (n : ℕ) : lambda n (1 : A) = if n ≤ 1 then 1 else 0 :=
  SpecialLambdaRing.lambda_unit n

theorem lambda_mul (n : ℕ) (a b : A) : lambda n (a * b) =
    MvPolynomial.aeval (Sum.elim (fun i : ℕ+ => lambda i a) (fun j : ℕ+ => lambda j b))
      (UniversalPolynomial.productPolynomial n) := SpecialLambdaRing.lambda_mul n a b

theorem lambda_iterate (n m : ℕ) (a : A) : lambda n (lambda m a) =
    MvPolynomial.aeval (fun i : ℕ+ => lambda i a)
      (UniversalPolynomial.iterationPolynomial n m) := SpecialLambdaRing.lambda_iterate n m a

-- The inner index zero gives precisely the exterior-power unit convention.
example (n : ℕ) (a : A) : lambda n (lambda 0 a) = if n ≤ 1 then 1 else 0 := by
  simp

example (a : A) : lambda 2 (lambda 0 a) = 0 := by simp

example (n : ℕ) (a : A) : lambda 0 (lambda n a) = 1 := by simp

end LambdaRing
