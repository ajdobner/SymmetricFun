import SymmetricFunctions.Lambda.Universal

/-!
# Integral plethysm

Substitute the inner symmetric function into the outer one using the universal
special lambda-ring evaluator. Coefficients of both functions are integers.
General coefficient-linear power-sum evaluation is a separate construction.
-/

noncomputable section

namespace SymmetricFunction

/-- Integral plethysm: the outer function is evaluated at the inner function. -/
def plethysm (f g : SymmetricFunction ℤ) : SymmetricFunction ℤ := lambdaEval g f

theorem plethysm_eq_lambdaEval (f g : SymmetricFunction ℤ) :
    plethysm f g = lambdaEval g f := rfl

/-- Elementary plethysm is an exterior power, including index zero. -/
@[simp] theorem plethysm_e (n : ℕ) (g : SymmetricFunction ℤ) :
    plethysm (e n) g = LambdaRing.lambda n g := lambdaEval_e g n

@[simp] theorem e_one_plethysm (g : SymmetricFunction ℤ) : plethysm (e 1) g = g :=
  lambdaEval_e_one g

@[simp] theorem plethysm_e_one (f : SymmetricFunction ℤ) : plethysm f (e 1) = f := by
  simp [plethysm, lambdaEval_self]

/-- Associativity is naturality of the universal evaluator. -/
theorem plethysm_assoc (f g k : SymmetricFunction ℤ) :
    plethysm (plethysm f g) k = plethysm f (plethysm g k) :=
  DFunLike.congr_fun (lambdaEval_natural (lambdaEval k) g) f

theorem add_plethysm (f g k : SymmetricFunction ℤ) :
    plethysm (f + g) k = plethysm f k + plethysm g k := map_add (lambdaEval k) f g

theorem mul_plethysm (f g k : SymmetricFunction ℤ) :
    plethysm (f * g) k = plethysm f k * plethysm g k := map_mul (lambdaEval k) f g

/-- Plethysm preserves exterior powers in the outer argument. -/
theorem lambda_plethysm (n : ℕ) (f g : SymmetricFunction ℤ) :
    plethysm (LambdaRing.lambda n f) g = LambdaRing.lambda n (plethysm f g) :=
  LambdaRingHom.map_lambda (lambdaEval g) n f

end SymmetricFunction
