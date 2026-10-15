import SymmetricFunctions.Stable
import LambdaRing.Polynomial.Special

/-! # The stable integral special lambda-ring structure -/

noncomputable section

namespace SymmetricFunction

open MvPolynomial LambdaRing.Polynomial

/-- Polynomial exterior powers preserve symmetry by permutation naturality. -/
theorem isSymmetric_operation {σ : Type*} {f : MvPolynomial σ ℤ}
    (hf : f.IsSymmetric) (n : ℕ) : (operation n f).IsSymmetric := by
  intro e
  rw [operation_rename, hf e]

/-- Exterior powers commute with adjoining or deleting the last zero variable. -/
theorem zeroLast_operation (N n : ℕ) (f : MvPolynomial (Fin (N + 1)) ℤ) :
    zeroLast ℤ N (operation n f) = operation n (zeroLast ℤ N f) := by
  apply operation_natural (zeroLast ℤ N).toRingHom
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

/-- Componentwise exterior power of a bounded compatible symmetric family. -/
def lambdaFamily (n : ℕ) (f : BoundedStable ℤ) : BoundedStable ℤ :=
  ⟨fun N => ⟨operation n (f.val N).val, isSymmetric_operation (f.val N).property n⟩,
    (by
      intro N
      apply Subtype.ext
      rw [coe_transition]
      change zeroLast ℤ N (operation n (f.val (N+1)).val) = operation n (f.val N).val
      rw [zeroLast_operation]
      have h := congrArg Subtype.val (f.property.1 N)
      rw [coe_transition] at h
      rw [h]),
    (by
      obtain ⟨d, hd⟩ := f.property.2
      exact ⟨n*d, fun N => operation_totalDegree_le n d (f.val N).val (hd N)⟩)⟩

@[simp] theorem lambdaFamily_apply (n N : ℕ) (f : BoundedStable ℤ) :
    ((lambdaFamily n f).val N).val = operation n (f.val N).val := rfl

/-- The same explicit bound works for every component after applying an exterior power. -/
theorem lambdaFamily_degree_bound (n : ℕ) (f : BoundedStable ℤ) {d : ℕ}
    (hd : ∀ N, (f.val N).val.totalDegree ≤ d) (N : ℕ) :
    ((lambdaFamily n f).val N).val.totalDegree ≤ n*d :=
  operation_totalDegree_le n d _ (hd N)

/-- Integral exterior powers transferred through the proved bounded stable equivalence. -/
def lambdaOperation (n : ℕ) (f : SymmetricFunction ℤ) : SymmetricFunction ℤ :=
  (stableEquiv ℤ).symm (lambdaFamily n (stableEquiv ℤ f))

/-- Exterior powers multiply a symmetric-function degree bound by the operation index. -/
theorem lambdaOperation_mem_degreeLE (n : ℕ) {f : SymmetricFunction ℤ} {d : ℕ}
    (hf : f ∈ degreeLE ℤ d) : lambdaOperation n f ∈ degreeLE ℤ (n*d) := by
  have hbase (K : ℕ) : ((stableEquiv ℤ f).val K).val.totalDegree ≤ d := by
    change (rho ℤ K f).val.totalDegree ≤ d
    exact (mem_finiteDegreeLE ℤ K d (rho ℤ K f)).mp (rho_mem_finiteDegreeLE ℤ K hf)
  have hb := lambdaFamily_degree_bound n (stableEquiv ℤ f) hbase
  rw [lambdaOperation, stableEquiv_symm_eq_lift ℤ _ hb le_rfl]
  exact liftSymmetric_mem_degreeLE ℤ (n*d)
    ((mem_finiteDegreeLE ℤ (n*d) (n*d) ((lambdaFamily n (stableEquiv ℤ f)).val (n*d))).mpr
      (hb (n*d)))

/-- Finite specialization as a ring homomorphism into the full polynomial ring. -/
def rhoPolynomial (N : ℕ) : SymmetricFunction ℤ →+* MvPolynomial (Fin N) ℤ :=
  (symmetricSubalgebra (Fin N) ℤ).val.toRingHom.comp (rho ℤ N).toRingHom

@[simp] theorem rhoPolynomial_apply (N : ℕ) (f : SymmetricFunction ℤ) :
    rhoPolynomial N f = (rho ℤ N f).val := rfl

/-- Finite compatibility holds at every size, including below the degree bound. -/
theorem rhoPolynomial_lambdaOperation (N n : ℕ) (f : SymmetricFunction ℤ) :
    rhoPolynomial N (lambdaOperation n f) = operation n (rhoPolynomial N f) := by
  simp only [rhoPolynomial_apply, lambdaOperation, rho_stableEquiv_symm,
    lambdaFamily_apply, stableEquiv_apply]

/-- All finite polynomial specializations jointly detect equality. -/
theorem eq_of_rhoPolynomial_eq {f g : SymmetricFunction ℤ}
    (h : ∀ N, rhoPolynomial N f = rhoPolynomial N g) : f = g := by
  apply stableMap_injective ℤ
  apply Subtype.ext
  funext N
  apply Subtype.ext
  exact h N

@[simp] theorem lambdaOperation_zero (f : SymmetricFunction ℤ) : lambdaOperation 0 f = 1 := by
  apply eq_of_rhoPolynomial_eq
  intro N
  rw [rhoPolynomial_lambdaOperation, operation_zero, map_one]

@[simp] theorem lambdaOperation_one (f : SymmetricFunction ℤ) : lambdaOperation 1 f = f := by
  apply eq_of_rhoPolynomial_eq
  intro N
  rw [rhoPolynomial_lambdaOperation, operation_one]

theorem lambdaOperation_add (n : ℕ) (f g : SymmetricFunction ℤ) :
    lambdaOperation n (f + g) = ∑ ij ∈ Finset.antidiagonal n,
      lambdaOperation ij.1 f * lambdaOperation ij.2 g := by
  apply eq_of_rhoPolynomial_eq
  intro N
  simp only [rhoPolynomial_lambdaOperation, map_add, operation_add, map_sum, map_mul]

instance : PreLambdaRing (SymmetricFunction ℤ) where
  lambdaOp := lambdaOperation
  lambda_zero := lambdaOperation_zero
  lambda_one := lambdaOperation_one
  lambda_add := lambdaOperation_add

@[simp] theorem lambda_eq_lambdaOperation (n : ℕ) (f : SymmetricFunction ℤ) :
    LambdaRing.lambda n f = lambdaOperation n f := rfl

/-- The stable unit convention is the exterior-power convention. -/
@[simp] theorem lambdaOperation_unit (n : ℕ) :
    lambdaOperation n (1 : SymmetricFunction ℤ) = if n ≤ 1 then 1 else 0 := by
  apply eq_of_rhoPolynomial_eq
  intro N
  rw [rhoPolynomial_lambdaOperation, map_one, operation_unit]
  split <;> simp

/-- The stable product identity is inherited from the actual finite special operations. -/
theorem lambdaOperation_mul (n : ℕ) (f g : SymmetricFunction ℤ) :
    lambdaOperation n (f * g) =
      aeval (Sum.elim (fun k : ℕ+ => lambdaOperation k f)
        (fun k : ℕ+ => lambdaOperation k g))
        (LambdaRing.UniversalPolynomial.productPolynomial n) := by
  apply eq_of_rhoPolynomial_eq
  intro N
  rw [rhoPolynomial_lambdaOperation, map_mul, operation_mul,
    map_int_aeval_sum (rhoPolynomial N)]
  simp only [rhoPolynomial_lambdaOperation]

/-- The stable iteration identity, with both indices allowed to be zero. -/
theorem lambdaOperation_iterate (n m : ℕ) (f : SymmetricFunction ℤ) :
    lambdaOperation n (lambdaOperation m f) =
      aeval (fun k : ℕ+ => lambdaOperation k f)
        (LambdaRing.UniversalPolynomial.iterationPolynomial n m) := by
  apply eq_of_rhoPolynomial_eq
  intro N
  rw [rhoPolynomial_lambdaOperation, rhoPolynomial_lambdaOperation, operation_iterate,
    map_int_aeval (rhoPolynomial N)]
  simp only [rhoPolynomial_lambdaOperation]

instance : SpecialLambdaRing (SymmetricFunction ℤ) where
  lambda_unit := lambdaOperation_unit
  lambda_mul := lambdaOperation_mul
  lambda_iterate := lambdaOperation_iterate

/-- Every finite integral specialization preserves all exterior powers. -/
def rhoLambdaHom (N : ℕ) : LambdaRingHom (SymmetricFunction ℤ) (MvPolynomial (Fin N) ℤ) :=
  { rhoPolynomial N with map_lambda' := rhoPolynomial_lambdaOperation N }

@[simp] theorem rhoLambdaHom_apply (N : ℕ) (f : SymmetricFunction ℤ) :
    rhoLambdaHom N f = (rho ℤ N f).val := rfl

/-- The elementary generators are exactly the exterior powers of e_1. -/
@[simp] theorem lambda_e_one (n : ℕ) : LambdaRing.lambda n (e (R := ℤ) 1) = e n := by
  apply eq_of_rhoPolynomial_eq
  intro N
  rw [lambda_eq_lambdaOperation, rhoPolynomial_lambdaOperation]
  simp only [rhoPolynomial_apply, rho_e, esymm_one]
  rw [operation_sum_lines (fun i : Fin N => X (R := ℤ) i) isLineMonomial_X]
  rfl

example : LambdaRing.lambda 0 (e (R := ℤ) 1) = 1 := by simp

example (n : ℕ) (f : SymmetricFunction ℤ) :
    (rho ℤ 0 (LambdaRing.lambda n f)).val = operation n (rho ℤ 0 f).val :=
  rhoPolynomial_lambdaOperation 0 n f

end SymmetricFunction
