import SymmetricFunctions.Completion.Hopf
import SymmetricFunctions.Completion.PolynomialRealization
import SymmetricFunctions.Hopf.Alphabets
import SymmetricFunctions.Finite.Weighted

/-! # Finite specialization of the total-degree completed tensor

The target has two independent finite alphabets. A coefficient uses exactly
one total-degree tensor component, so every output coefficient is defined.
-/
noncomputable section
namespace SymmetricFunction
open SymmetricFunctions
open scoped TensorProduct
variable (R : Type*) [CommRing R]

/-- Finite tensor specialization preserves the sum of the two alphabet degrees. -/
theorem isHomogeneous_tensorAlphabetSpecialization (M N d : ℕ)
    (z : SymmetricFunction R ⊗[R] SymmetricFunction R) (hz : z ∈ tensorDegree R d) :
    (tensorAlphabetSpecialization R (Fin M) (Fin N) z).IsHomogeneous d := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, j, f, g, rfl, hf, hg, rfl⟩ := hz
    rw [tensorAlphabetSpecialization_tmul, alphabetSpecialization_fin, alphabetSpecialization_fin]
    exact ((isHomogeneous_rho R M i f hf).rename_isHomogeneous).mul
      ((isHomogeneous_rho R N j g hg).rename_isHomogeneous)
  | zero => rw [map_zero]; exact (MvPolynomial.homogeneousSubmodule (Fin M ⊕ Fin N) R d).zero_mem
  | add x y hx hy ihx ihy => rw [map_add]; exact ihx.add ihy
  | smul r x hx ih =>
    rw [map_smul]
    exact (MvPolynomial.homogeneousSubmodule (Fin M ⊕ Fin N) R d).smul_mem r ih

/-- Specialize a completed tensor in two genuine finite alphabets. -/
def completedTensorSpecialization (M N : ℕ) :
    CompletedTensor R →ₐ[R] MvPowerSeries (Fin M ⊕ Fin N) R :=
  GradedCompletion.polynomialRealization (tensorDegree R)
    (tensorAlphabetSpecialization R (Fin M) (Fin N))
    (isHomogeneous_tensorAlphabetSpecialization R M N)

/-- An exponent coefficient reads only its total-degree component. -/
@[simp] theorem coeff_completedTensorSpecialization (M N : ℕ) (F : CompletedTensor R)
    (a : (Fin M ⊕ Fin N) →₀ ℕ) :
    MvPowerSeries.coeff a (completedTensorSpecialization R M N F) =
      (tensorAlphabetSpecialization R (Fin M) (Fin N)
        (CompletedTensor.component R F a.degree)).coeff a := rfl

/-- Completed homogeneous projection agrees with bounded tensor specialization. -/
theorem homogeneousComponent_completedTensorSpecialization (M N : ℕ)
    (F : CompletedTensor R) (d : ℕ) :
    MvPowerSeries.homogeneousComponent d (completedTensorSpecialization R M N F) =
      (tensorAlphabetSpecialization R (Fin M) (Fin N)
        (CompletedTensor.component R F d) : MvPowerSeries (Fin M ⊕ Fin N) R) :=
  (GradedCompletion.polynomialRealization_component _ _ _ F d).symm

/-- Homogeneous bounded tensors are placed in their own degree before specialization. -/
theorem completedTensorSpecialization_homogeneous (M N : ℕ) {d : ℕ}
    {z : SymmetricFunction R ⊗[R] SymmetricFunction R} (hz : z ∈ tensorDegree R d) :
    completedTensorSpecialization R M N (tensorCompletionMap R z) =
      (tensorAlphabetSpecialization R (Fin M) (Fin N) z : MvPowerSeries (Fin M ⊕ Fin N) R) := by
  have he : tensorCompletionMap R z = GradedCompletion.single (tensorDegree R) d z hz := by
    apply GradedCompletion.ext
    intro n
    exact component_tensorCompletionMap_of_mem R hz n
  rw [he]
  exact GradedCompletion.polynomialRealization_single _ _ _ _ _ _

/-- The completed map agrees with the original polynomial map on every bounded tensor. -/
@[simp] theorem completedTensorSpecialization_bounded (M N : ℕ)
    (z : SymmetricFunction R ⊗[R] SymmetricFunction R) :
    completedTensorSpecialization R M N (tensorCompletionMap R z) =
      (tensorAlphabetSpecialization R (Fin M) (Fin N) z : MvPowerSeries (Fin M ⊕ Fin N) R) := by
  have he : (completedTensorSpecialization R M N).comp (tensorCompletionMap R) =
      (MvPolynomial.coeToMvPowerSeries.algHom R).comp
        (tensorAlphabetSpecialization R (Fin M) (Fin N)) := by
    apply Algebra.TensorProduct.ext
    · apply algHom_ext
      intro i
      change completedTensorSpecialization R M N (tensorCompletionMap R (e i ⊗ₜ[R] 1)) = _
      rw [completedTensorSpecialization_homogeneous R M N
        (tmul_mem_tensorDegree (isHomogeneous_e i) isHomogeneous_one)]
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
        MvPolynomial.coeToMvPowerSeries.algHom_apply, Algebra.algebraMap_self, MvPowerSeries.map_id,
        RingHom.id_apply]
    · apply algHom_ext
      intro i
      change completedTensorSpecialization R M N (tensorCompletionMap R (1 ⊗ₜ[R] e i)) = _
      rw [completedTensorSpecialization_homogeneous R M N
        (tmul_mem_tensorDegree isHomogeneous_one (isHomogeneous_e i))]
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeRight_apply,
        MvPolynomial.coeToMvPowerSeries.algHom_apply, Algebra.algebraMap_self, MvPowerSeries.map_id,
        RingHom.id_apply]
  simpa only [AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply,
    Algebra.algebraMap_self, MvPowerSeries.map_id,
        RingHom.id_apply] using AlgHom.congr_fun he z

end SymmetricFunction
