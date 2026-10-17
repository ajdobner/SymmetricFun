import LambdaRing.Transport

/-! # Pointwise special lambda structures

Products of arbitrary special lambda rings have pointwise exterior powers.
No torsion or characteristic hypothesis is needed.
-/

noncomputable section

namespace LambdaRing

variable {ι : Type*} {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, PreLambdaRing (A i)]

instance piPreLambdaRing : PreLambdaRing (∀ i, A i) where
  lambdaOp n a i := lambda n (a i)
  lambda_zero a := funext fun i => lambda_zero (a i)
  lambda_one a := funext fun i => lambda_one (a i)
  lambda_add n a b := by
    funext i
    simpa only [Finset.sum_apply, Pi.mul_apply, Pi.add_apply] using lambda_add n (a i) (b i)

@[simp] theorem lambda_apply (n : ℕ) (a : ∀ i, A i) (i : ι) :
    lambda n a i = lambda n (a i) := rfl

instance piSpecialLambdaRing [∀ i, SpecialLambdaRing (A i)] : SpecialLambdaRing (∀ i, A i) where
  lambda_unit n := by
    funext i
    change lambda n (1 : A i) = (if n ≤ 1 then (1 : ∀ i, A i) else 0) i
    rw [lambda_unit]
    split <;> rfl
  lambda_mul n a b := by
    funext i
    change lambda n (a i * b i) = (Pi.evalRingHom A i) (_)
    rw [MvPolynomial.hom_eval₂]
    convert lambda_mul n (a i) (b i) using 1
    congr 1
    funext j
    cases j <;> rfl
  lambda_iterate n m a := by
    funext i
    change lambda n (lambda m (a i)) = (Pi.evalRingHom A i) (_)
    rw [MvPolynomial.hom_eval₂]
    convert lambda_iterate n m (a i) using 1
    congr 1

/-- Evaluation at a coordinate preserves exterior powers. -/
def evaluationHom (i : ι) : LambdaRingHom (∀ i, A i) (A i) :=
  { Pi.evalRingHom A i with map_lambda' := fun _ _ => rfl }

end LambdaRing
