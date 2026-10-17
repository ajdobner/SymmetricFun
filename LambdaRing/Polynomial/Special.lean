import LambdaRing.Polynomial.Density
import LambdaRing.Polynomial.Degree

/-! # The special lambda-ring structure on integral polynomial rings

Both universal identities are proved for signed coefficients by descent of the
rational coefficient-parameter identities. No assumption on an eventual target
lambda ring, such as torsion-freeness, enters this construction.
-/

noncomputable section

namespace LambdaRing.Polynomial

open MvPolynomial UniversalPolynomial

variable {σ τ : Type*}

/-- The universal product identity for arbitrary signed integer polynomials. -/
theorem operation_mul (f g : MvPolynomial σ ℤ) (n : ℕ) :
    operation n (f * g) = aeval (Sum.elim (fun k : ℕ+ => operation k f)
      (fun k : ℕ+ => operation k g)) (productPolynomial n) := by
  apply map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [map_operation_eq_rationalOperation, map_mul,
    map_int_aeval_sum (map (Int.castRingHom ℚ))]
  simp only [map_operation_eq_rationalOperation]
  exact rationalOperation_mul _ _ n

/-- The universal iteration identity for arbitrary signed integer polynomials. -/
theorem operation_iterate (f : MvPolynomial σ ℤ) (n m : ℕ) :
    operation n (operation m f) =
      aeval (fun k : ℕ+ => operation k f) (iterationPolynomial n m) := by
  apply map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [map_operation_eq_rationalOperation, map_operation_eq_rationalOperation,
    map_int_aeval (map (Int.castRingHom ℚ))]
  simp only [map_operation_eq_rationalOperation]
  exact rationalOperation_iterate _ n m

/-- The actual special structure on the previously constructed integral polynomial operations. -/
instance : SpecialLambdaRing (MvPolynomial σ ℤ) where
  lambda_unit := operation_unit
  lambda_mul := fun n f g => operation_mul f g n
  lambda_iterate := fun n m f => operation_iterate f n m

/-- Any renaming is a morphism of the constructed special lambda rings. -/
def renameHom (r : σ → τ) : LambdaRingHom (MvPolynomial σ ℤ) (MvPolynomial τ ℤ) :=
  monomialHom (rename r).toRingHom (by intro i; simp)

@[simp] theorem renameHom_apply (r : σ → τ) (f : MvPolynomial σ ℤ) :
    renameHom r f = rename r f := rfl

/-- Setting any selected variables to zero is a special lambda-ring morphism. -/
def setZeroHom (keep : σ → Prop) [DecidablePred keep] :
    LambdaRingHom (MvPolynomial σ ℤ) (MvPolynomial σ ℤ) :=
  { (aeval (fun i => if keep i then X i else (0 : MvPolynomial σ ℤ))).toRingHom with
    map_lambda' := operation_setZero keep }

@[simp] theorem setZeroHom_apply (keep : σ → Prop) [DecidablePred keep]
    (f : MvPolynomial σ ℤ) : setZeroHom keep f =
      aeval (fun i => if keep i then X i else (0 : MvPolynomial σ ℤ)) f := rfl

-- These use the proved special instance, with a negative coefficient and index zero.
example (i : σ) : LambdaRing.lambda 2 (-X i : MvPolynomial σ ℤ) = X i ^ 2 := by
  change operation 2 (-(monomial (Finsupp.single i 1) (1 : ℤ))) = _
  rw [← map_neg, operation_monomial_neg_one, neg_sq]
  rfl

example (f : MvPolynomial σ ℤ) : LambdaRing.lambda 2 (LambdaRing.lambda 0 f) = 0 := by
  simp

end LambdaRing.Polynomial
