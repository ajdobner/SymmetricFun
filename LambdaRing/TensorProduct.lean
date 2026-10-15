import SymmetricFunctions.Hopf.TensorSpecialization
import SymmetricFunctions.Lambda.Universal
import LambdaRing.Pi
import LambdaRing.Subring

/-! # The special lambda structure on the integral symmetric-function tensor square

Finite disjoint alphabets jointly embed the tensor square into a product of
actual polynomial lambda rings. Its image is closed under exterior powers by
the integral special identities. This constructs the needed tensor structure;
it does not equip arbitrary elementary polynomial variables with line operations.
-/

noncomputable section

namespace SymmetricFunction

open scoped TensorProduct
open LambdaRing

/-- All finite pairs of alphabets, with the actual polynomial lambda structures. -/
abbrev TensorAlphabetFamily := (s : ℕ × ℕ) → MvPolynomial (Fin s.1 ⊕ Fin s.2) ℤ

/-- Simultaneously specialize a tensor to every pair of finite alphabets. -/
def tensorAlphabetEmbedding :
    (SymmetricFunction ℤ ⊗[ℤ] SymmetricFunction ℤ) →+* TensorAlphabetFamily :=
  RingHom.pi fun s => (tensorAlphabetSpecialization ℤ (Fin s.1) (Fin s.2)).toRingHom

@[simp] theorem tensorAlphabetEmbedding_apply
    (x : SymmetricFunction ℤ ⊗[ℤ] SymmetricFunction ℤ) (s : ℕ × ℕ) :
    tensorAlphabetEmbedding x s = tensorAlphabetSpecialization ℤ (Fin s.1) (Fin s.2) x := rfl

theorem tensorAlphabetEmbedding_injective : Function.Injective tensorAlphabetEmbedding := by
  intro x y h
  apply eq_of_tensorAlphabetSpecialization_eq ℤ
  intro N M
  exact congrFun h (N,M)

private theorem embedding_left_lambda (n : ℕ) (f : SymmetricFunction ℤ) :
    tensorAlphabetEmbedding (lambda n f ⊗ₜ[ℤ] 1) =
      lambda n (tensorAlphabetEmbedding (f ⊗ₜ[ℤ] 1)) := by
  funext s
  simp only [tensorAlphabetEmbedding_apply, tensorAlphabetSpecialization_tmul,
    map_one, mul_one, lambda_apply, alphabetSpecialization_fin]
  change MvPolynomial.rename Sum.inl (rhoPolynomial s.1 (lambda n f)) =
    lambda n (MvPolynomial.rename Sum.inl (rhoPolynomial s.1 f))
  rw [show rhoPolynomial s.1 (lambda n f) = lambda n (rhoPolynomial s.1 f) from
    (rhoLambdaHom s.1).map_lambda n f]
  exact LambdaRing.Polynomial.operation_rename _ _ _

private theorem embedding_right_lambda (n : ℕ) (f : SymmetricFunction ℤ) :
    tensorAlphabetEmbedding (1 ⊗ₜ[ℤ] lambda n f) =
      lambda n (tensorAlphabetEmbedding (1 ⊗ₜ[ℤ] f)) := by
  funext s
  simp only [tensorAlphabetEmbedding_apply, tensorAlphabetSpecialization_tmul,
    map_one, one_mul, lambda_apply, alphabetSpecialization_fin]
  change MvPolynomial.rename Sum.inr (rhoPolynomial s.2 (lambda n f)) =
    lambda n (MvPolynomial.rename Sum.inr (rhoPolynomial s.2 f))
  rw [show rhoPolynomial s.2 (lambda n f) = lambda n (rhoPolynomial s.2 f) from
    (rhoLambdaHom s.2).map_lambda n f]
  exact LambdaRing.Polynomial.operation_rename _ _ _

/-- The image in all finite alphabets is closed under every exterior power. -/
theorem lambda_mem_range_tensorAlphabetEmbedding (n : ℕ)
    (x : SymmetricFunction ℤ ⊗[ℤ] SymmetricFunction ℤ) :
    lambda n (tensorAlphabetEmbedding x) ∈ tensorAlphabetEmbedding.range := by
  let S := lambdaStableSubring tensorAlphabetEmbedding.range
  have hl (f : SymmetricFunction ℤ) : tensorAlphabetEmbedding (f ⊗ₜ[ℤ] 1) ∈ S := by
    intro k
    exact ⟨lambda k f ⊗ₜ[ℤ] 1, embedding_left_lambda k f⟩
  have hr (f : SymmetricFunction ℤ) : tensorAlphabetEmbedding (1 ⊗ₜ[ℤ] f) ∈ S := by
    intro k
    exact ⟨1 ⊗ₜ[ℤ] lambda k f, embedding_right_lambda k f⟩
  have hx : tensorAlphabetEmbedding x ∈ S := by
    induction x using TensorProduct.inductionOn with
    | tmul f g =>
      have he : f ⊗ₜ[ℤ] g = (f ⊗ₜ[ℤ] 1) * (1 ⊗ₜ[ℤ] g) := by simp
      rw [he, map_mul]
      exact S.mul_mem (hl f) (hr g)
    | add x y hx hy => rw [map_add]; exact S.add_mem hx hy
  exact hx n

/-- The uniquely determined tensor exterior power reflected by finite alphabets. -/
def tensorLambdaOperation (n : ℕ) (x : SymmetricFunction ℤ ⊗[ℤ] SymmetricFunction ℤ) :
    SymmetricFunction ℤ ⊗[ℤ] SymmetricFunction ℤ :=
  Classical.choose (lambda_mem_range_tensorAlphabetEmbedding n x)

theorem tensorAlphabetEmbedding_tensorLambdaOperation (n : ℕ)
    (x : SymmetricFunction ℤ ⊗[ℤ] SymmetricFunction ℤ) :
    tensorAlphabetEmbedding (tensorLambdaOperation n x) = lambda n (tensorAlphabetEmbedding x) :=
  Classical.choose_spec (lambda_mem_range_tensorAlphabetEmbedding n x)

instance tensorPreLambdaRing : PreLambdaRing (SymmetricFunction ℤ ⊗[ℤ] SymmetricFunction ℤ) :=
  PreLambdaRing.ofInjective tensorAlphabetEmbedding tensorAlphabetEmbedding_injective
    tensorLambdaOperation tensorAlphabetEmbedding_tensorLambdaOperation

instance tensorSpecialLambdaRing :
    SpecialLambdaRing (SymmetricFunction ℤ ⊗[ℤ] SymmetricFunction ℤ) :=
  SpecialLambdaRing.ofInjective tensorAlphabetEmbedding tensorAlphabetEmbedding_injective
    tensorAlphabetEmbedding_tensorLambdaOperation

/-- Finite alphabet specialization preserves all tensor exterior powers. -/
theorem tensorAlphabetSpecialization_lambda (n N M : ℕ)
    (x : SymmetricFunction ℤ ⊗[ℤ] SymmetricFunction ℤ) :
    tensorAlphabetSpecialization ℤ (Fin N) (Fin M) (lambda n x) =
      lambda n (tensorAlphabetSpecialization ℤ (Fin N) (Fin M) x) :=
  congrFun (tensorAlphabetEmbedding_tensorLambdaOperation n x) (N,M)

@[simp] theorem lambda_tmul_one (n : ℕ) (f : SymmetricFunction ℤ) :
    lambda n (f ⊗ₜ[ℤ] (1 : SymmetricFunction ℤ)) = lambda n f ⊗ₜ[ℤ] 1 := by
  apply tensorAlphabetEmbedding_injective
  exact (tensorAlphabetEmbedding_tensorLambdaOperation n _).trans
    (embedding_left_lambda n f).symm

@[simp] theorem lambda_one_tmul (n : ℕ) (f : SymmetricFunction ℤ) :
    lambda n ((1 : SymmetricFunction ℤ) ⊗ₜ[ℤ] f) = 1 ⊗ₜ[ℤ] lambda n f := by
  apply tensorAlphabetEmbedding_injective
  exact (tensorAlphabetEmbedding_tensorLambdaOperation n _).trans
    (embedding_right_lambda n f).symm

/-- The left inclusion into the tensor square is a special lambda morphism. -/
def tensorLeftLambdaHom : LambdaRingHom (SymmetricFunction ℤ)
    (SymmetricFunction ℤ ⊗[ℤ] SymmetricFunction ℤ) :=
  { (Algebra.TensorProduct.includeLeft (R := ℤ) (S := ℤ)).toRingHom with
    map_lambda' := fun n f => (lambda_tmul_one n f).symm }

/-- The right inclusion into the tensor square is a special lambda morphism. -/
def tensorRightLambdaHom : LambdaRingHom (SymmetricFunction ℤ)
    (SymmetricFunction ℤ ⊗[ℤ] SymmetricFunction ℤ) :=
  { (Algebra.TensorProduct.includeRight (R := ℤ)).toRingHom with
    map_lambda' := fun n f => (lambda_one_tmul n f).symm }

end SymmetricFunction
