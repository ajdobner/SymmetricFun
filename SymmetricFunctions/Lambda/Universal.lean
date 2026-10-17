import SymmetricFunctions.Lambda.Structure
import SymmetricFunctions.BaseChange
import LambdaRing.Preservation

/-! # The free special lambda ring on one generator

The target is arbitrary, including special lambda rings with additive torsion.
Preservation is proved on every expression using the integral special identities.
-/

noncomputable section

namespace SymmetricFunction

open LambdaRing

variable {A B : Type*} [CommRing A] [PreLambdaRing A] [SpecialLambdaRing A]
variable [CommRing B] [PreLambdaRing B] [SpecialLambdaRing B]

/-- The underlying ring map sends e_i to the ith exterior power of the chosen element. -/
def lambdaEvaluation (a : A) : SymmetricFunction ℤ →+* A :=
  eval₂ (Int.castRingHom A) (fun i : ℕ+ => lambda i a)

omit [SpecialLambdaRing A] in
@[simp] theorem lambdaEvaluation_e (a : A) (n : ℕ) :
    lambdaEvaluation a (e n) = lambda n a := by
  cases n with
  | zero => simp [lambdaEvaluation]
  | succ n =>
    exact eval₂_e (Int.castRingHom A) (fun i : ℕ+ => lambda i a) (Nat.succPNat n)

omit [SpecialLambdaRing A] in
/-- The map preserves every exterior power at the distinguished generator. -/
theorem lambdaEvaluation_preserves_e_one (a : A) :
    PreservesAt (lambdaEvaluation a) (e 1) := by
  intro n
  rw [lambda_e_one, lambdaEvaluation_e, lambdaEvaluation_e, lambda_one]

/-- Preservation holds on every symmetric function, including arbitrary signed expressions. -/
theorem lambdaEvaluation_preserves (a : A) (f : SymmetricFunction ℤ) :
    PreservesAt (lambdaEvaluation a) f := by
  let S := preservingSubring (lambdaEvaluation a)
  have he (i : ℕ+) : e (i : ℕ) ∈ S := by
    have h := (lambdaEvaluation_preserves_e_one a).lambda (i : ℕ)
    rw [lambda_e_one] at h
    exact h
  change f ∈ S
  induction f using SymmetricFunction.induction_on with
  | C r =>
    rw [show algebraMap ℤ (SymmetricFunction ℤ) r = (r : SymmetricFunction ℤ) from
      map_intCast (algebraMap ℤ (SymmetricFunction ℤ)) r]
    exact intCast_mem S r
  | add f g hf hg => exact S.add_mem hf hg
  | mul_e f i hf => exact S.mul_mem hf (he i)

/-- The unique special lambda-ring morphism with chosen image of e_1. -/
def lambdaEval (a : A) : LambdaRingHom (SymmetricFunction ℤ) A :=
  { lambdaEvaluation a with
    map_lambda' := fun n f => lambdaEvaluation_preserves a f n }

@[simp] theorem lambdaEval_apply (a : A) (f : SymmetricFunction ℤ) :
    lambdaEval a f = lambdaEvaluation a f := rfl

@[simp] theorem lambdaEval_e (a : A) (n : ℕ) : lambdaEval a (e n) = lambda n a :=
  lambdaEvaluation_e a n

@[simp] theorem lambdaEval_e_one (a : A) : lambdaEval a (e 1) = a := by
  rw [lambdaEval_e, lambda_one]

omit [SpecialLambdaRing A] in
/-- Any preserving morphism is forced on every elementary generator by its value on e_1. -/
theorem lambdaHom_e (φ : LambdaRingHom (SymmetricFunction ℤ) A) (n : ℕ) :
    φ (e n) = lambda n (φ (e 1)) := by
  rw [← lambda_e_one n, LambdaRingHom.map_lambda]

omit [SpecialLambdaRing A] in
/-- Extensionality for lambda morphisms out of the integral symmetric functions. -/
theorem lambdaHom_ext {φ ψ : LambdaRingHom (SymmetricFunction ℤ) A}
    (h : φ (e 1) = ψ (e 1)) : φ = ψ := by
  apply LambdaRingHom.toRingHom_injective
  apply ringHom_ext
  · intro r
    rw [show algebraMap ℤ (SymmetricFunction ℤ) r = (r : SymmetricFunction ℤ) from
      map_intCast (algebraMap ℤ (SymmetricFunction ℤ)) r]
    simp only [map_intCast]
  · intro i
    change φ (e (i : ℕ)) = ψ (e (i : ℕ))
    rw [lambdaHom_e φ (i : ℕ), lambdaHom_e ψ (i : ℕ), h]

theorem lambdaEval_unique (a : A) (φ : LambdaRingHom (SymmetricFunction ℤ) A)
    (h : φ (e 1) = a) : φ = lambdaEval a :=
  lambdaHom_ext (h.trans (lambdaEval_e_one a).symm)

/-- Freeness on one generator, for every special lambda target, with no torsion restriction. -/
def lambdaHomEquiv (A : Type*) [CommRing A] [PreLambdaRing A] [SpecialLambdaRing A] :
    LambdaRingHom (SymmetricFunction ℤ) A ≃ A where
  toFun φ := φ (e 1)
  invFun := lambdaEval
  left_inv φ := lambdaHom_ext (lambdaEval_e_one (φ (e 1)))
  right_inv := lambdaEval_e_one

@[simp] theorem lambdaHomEquiv_apply (φ : LambdaRingHom (SymmetricFunction ℤ) A) :
    lambdaHomEquiv A φ = φ (e 1) := rfl

@[simp] theorem lambdaHomEquiv_symm_apply (a : A) :
    (lambdaHomEquiv A).symm a = lambdaEval a := rfl

/-- Naturality of the universal evaluator under every preserving target morphism. -/
theorem lambdaEval_natural (ψ : LambdaRingHom A B) (a : A) :
    ψ.comp (lambdaEval a) = lambdaEval (ψ a) := by
  apply lambdaHom_ext
  simp only [LambdaRingHom.comp_apply, lambdaEval_e_one]

/-- Evaluation at e_1 is the natural forward map of the free-object equivalence. -/
theorem lambdaHomEquiv_natural (ψ : LambdaRingHom A B)
    (φ : LambdaRingHom (SymmetricFunction ℤ) A) :
    lambdaHomEquiv B (ψ.comp φ) = ψ (lambdaHomEquiv A φ) := rfl

@[simp] theorem lambdaEval_self : lambdaEval (e (R := ℤ) 1) = LambdaRingHom.id _ := by
  apply lambdaHom_ext
  rw [lambdaEval_e_one, LambdaRingHom.id_apply]

-- The identity and both inverse laws use the actual constructed special source instance.
example (f : SymmetricFunction ℤ) : lambdaEval (e (R := ℤ) 1) f = f := by
  rw [lambdaEval_self, LambdaRingHom.id_apply]

example (a : A) : lambdaHomEquiv A ((lambdaHomEquiv A).symm a) = a :=
  (lambdaHomEquiv A).apply_symm_apply a

end SymmetricFunction
