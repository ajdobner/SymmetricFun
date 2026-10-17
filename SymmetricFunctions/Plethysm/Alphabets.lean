import LambdaRing.TensorProduct
import SymmetricFunctions.Plethysm.Adams

/-! # Integral plethysm and Hopf alphabet addition

The tensor square carries the actual special lambda structure constructed from
finite alphabets. Comultiplication evaluates at the sum of its two universal
letters, so it preserves exterior powers and integral plethysm.
-/

noncomputable section

namespace SymmetricFunction

open scoped TensorProduct
open LambdaRing

/-- The coproduct evaluates at the sum of the two independent universal alphabets. -/
theorem comultiplication_eq_lambdaEval (f : SymmetricFunction ℤ) :
    comultiplication f = lambdaEval
      (e (R := ℤ) 1 ⊗ₜ[ℤ] 1 + 1 ⊗ₜ[ℤ] e (R := ℤ) 1) f := by
  have he : (comultiplication (R := ℤ)).toRingHom =
      (lambdaEval (e (R := ℤ) 1 ⊗ₜ[ℤ] 1 + 1 ⊗ₜ[ℤ] e (R := ℤ) 1)).toRingHom := by
    apply ringHom_ext
    · intro z
      rw [show algebraMap ℤ (SymmetricFunction ℤ) z = (z : SymmetricFunction ℤ) from
        map_intCast (algebraMap ℤ (SymmetricFunction ℤ)) z]
      simp only [map_intCast]
    · intro i
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, comultiplication_e,
        LambdaRingHom.coe_toRingHom, lambdaEval_e, lambda_add,
        lambda_tmul_one, lambda_one_tmul, lambda_e_one]
      apply Finset.sum_congr rfl
      intro ij _
      simp
  exact DFunLike.congr_fun he f

/-- The actual Hopf coproduct is a special lambda morphism. -/
def comultiplicationLambdaHom : LambdaRingHom (SymmetricFunction ℤ)
    (SymmetricFunction ℤ ⊗[ℤ] SymmetricFunction ℤ) :=
  { (comultiplication (R := ℤ)).toRingHom with
    map_lambda' := fun n f => by
      change comultiplication (lambda n f) = lambda n (comultiplication f)
      rw [comultiplication_eq_lambdaEval, LambdaRingHom.map_lambda,
        ← comultiplication_eq_lambdaEval] }

@[simp] theorem comultiplicationLambdaHom_apply (f : SymmetricFunction ℤ) :
    comultiplicationLambdaHom f = comultiplication f := rfl

theorem comultiplication_lambda (n : ℕ) (f : SymmetricFunction ℤ) :
    comultiplication (lambda n f) = lambda n (comultiplication f) :=
  comultiplicationLambdaHom.map_lambda n f

/-- Substitution commutes with alphabet addition through the proved tensor lambda structure. -/
theorem comultiplication_plethysm (f g : SymmetricFunction ℤ) :
    comultiplication (plethysm f g) = lambdaEval (comultiplication g) f :=
  DFunLike.congr_fun (lambdaEval_natural comultiplicationLambdaHom g) f

end SymmetricFunction
