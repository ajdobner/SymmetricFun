import SymmetricFunctions.Completion.Omega
import SymmetricFunctions.Completion.Single
import SymmetricFunctions.Hopf.Grading
import SymmetricFunctions.Hopf.Series

/-! # Coproduct into the total-degree completed tensor

The target is a product of total-degree pieces of the bounded tensor algebra.
It is not the ordinary algebraic tensor product of two completions.
-/
noncomputable section
namespace SymmetricFunction
open SymmetricFunctions
open scoped TensorProduct
variable (R : Type*) [CommRing R]
attribute [local irreducible] SymmetricFunction

/-- Product of the total-degree tensor pieces, with finite convolution. -/
abbrev CompletedTensor := GradedCompletion (tensorDegree R)

namespace CompletedTensor
/-- The total-degree component, counting degrees in both tensor factors. -/
abbrev component (F : CompletedTensor R) (n : ℕ) :
    SymmetricFunction R ⊗[R] SymmetricFunction R :=
  GradedCompletion.component (tensorDegree R) F n
theorem component_mul (F G : CompletedTensor R) (n : ℕ) :
    component R (F * G) n = ∑ ij ∈ Finset.antidiagonal n,
      component R F ij.1 * component R G ij.2 := GradedCompletion.component_mul _ F G n
@[simp] theorem component_zero (n : ℕ) : component R 0 n = 0 :=
  GradedCompletion.component_zero _ n
@[simp] theorem component_add (F G : CompletedTensor R) (n : ℕ) :
    component R (F + G) n = component R F n + component R G n :=
  GradedCompletion.component_add _ F G n
@[simp] theorem component_smul (r : R) (F : CompletedTensor R) (n : ℕ) :
    component R (r • F) n = r • component R F n :=
  GradedCompletion.component_smul _ r F n
end CompletedTensor

/-- The original coproduct extends by preserving each total degree. -/
def completedCoproduct : DegreeCompletion R →ₐ[R] CompletedTensor R :=
  GradedCompletion.map (homogeneousSubmodule R) (tensorDegree R) comultiplication
    (fun _ _ hf => comultiplication_mem_tensorDegree hf)

@[simp] theorem component_completedCoproduct (F : DegreeCompletion R) (n : ℕ) :
    CompletedTensor.component R (completedCoproduct R F) n =
      comultiplication (DegreeCompletion.component R F n) :=
  GradedCompletion.component_map _ _ _ _ _ _

private theorem includeLeft_mem_degree (n : ℕ) (f : SymmetricFunction R)
    (hf : IsHomogeneous f n) :
    (Algebra.TensorProduct.includeLeft : SymmetricFunction R →ₐ[R]
      SymmetricFunction R ⊗[R] SymmetricFunction R) f ∈ tensorDegree R n := by
  simpa only [Algebra.TensorProduct.includeLeft_apply, add_zero] using
    tmul_mem_tensorDegree hf (isHomogeneous_one (R := R))

private theorem includeRight_mem_degree (n : ℕ) (f : SymmetricFunction R)
    (hf : IsHomogeneous f n) :
    (Algebra.TensorProduct.includeRight : SymmetricFunction R →ₐ[R]
      SymmetricFunction R ⊗[R] SymmetricFunction R) f ∈ tensorDegree R n := by
  simpa only [Algebra.TensorProduct.includeRight_apply, zero_add] using
    tmul_mem_tensorDegree (isHomogeneous_one (R := R)) hf

/-- The left alphabet inclusion into the completed tensor. -/
def completedTensorLeft : DegreeCompletion R →ₐ[R] CompletedTensor R :=
  GradedCompletion.map (homogeneousSubmodule R) (tensorDegree R)
    Algebra.TensorProduct.includeLeft (includeLeft_mem_degree R)

/-- The right alphabet inclusion into the completed tensor. -/
def completedTensorRight : DegreeCompletion R →ₐ[R] CompletedTensor R :=
  GradedCompletion.map (homogeneousSubmodule R) (tensorDegree R)
    Algebra.TensorProduct.includeRight (includeRight_mem_degree R)

@[simp] theorem component_completedTensorLeft (F : DegreeCompletion R) (n : ℕ) :
    CompletedTensor.component R (completedTensorLeft R F) n =
      DegreeCompletion.component R F n ⊗ₜ[R] 1 := rfl

@[simp] theorem component_completedTensorRight (F : DegreeCompletion R) (n : ℕ) :
    CompletedTensor.component R (completedTensorRight R F) n =
      1 ⊗ₜ[R] DegreeCompletion.component R F n := rfl

/-- External product of two completed alphabets in the total-degree completed tensor. -/
def completedTensorProduct (F G : DegreeCompletion R) : CompletedTensor R :=
  completedTensorLeft R F * completedTensorRight R G

theorem component_completedTensorProduct (F G : DegreeCompletion R) (n : ℕ) :
    CompletedTensor.component R (completedTensorProduct R F G) n =
      ∑ ij ∈ Finset.antidiagonal n,
        DegreeCompletion.component R F ij.1 ⊗ₜ[R] DegreeCompletion.component R G ij.2 := by
  rw [completedTensorProduct, CompletedTensor.component_mul]
  simp only [component_completedTensorLeft, component_completedTensorRight,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Ω is group-like in the appropriate completed tensor target. -/
theorem completedCoproduct_completeSeries :
    completedCoproduct R completeSeries =
      completedTensorProduct R completeSeries completeSeries := by
  apply GradedCompletion.ext
  intro n
  change CompletedTensor.component R _ n = CompletedTensor.component R _ n
  rw [component_completedCoproduct, component_completeSeries, component_completedTensorProduct]
  simp only [component_completeSeries, comultiplication_h]

/-- The canonical map from the bounded tensor algebra to its degree completion. -/
def tensorCompletionMap :
    SymmetricFunction R ⊗[R] SymmetricFunction R →ₐ[R] CompletedTensor R :=
  Algebra.TensorProduct.lift
    ((completedTensorLeft R).comp (completionEmbedding R))
    ((completedTensorRight R).comp (completionEmbedding R)) (fun _ _ => Commute.all _ _)

@[simp] theorem tensorCompletionMap_tmul (f g : SymmetricFunction R) :
    tensorCompletionMap R (f ⊗ₜ[R] g) =
      completedTensorProduct R (completionEmbedding R f) (completionEmbedding R g) :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- Homogeneous bounded functions embed in exactly one completed degree. -/
theorem completionEmbedding_of_homogeneous {f : SymmetricFunction R} {n : ℕ}
    (hf : IsHomogeneous f n) :
    completionEmbedding R f = GradedCompletion.single (homogeneousSubmodule R) n f hf := by
  apply DegreeCompletion.ext
  intro k
  rw [component_completionEmbedding]
  change homogeneousComponent k f = if k = n then f else 0
  split_ifs with hk
  · subst k; exact homogeneousComponent_of_mem hf
  · exact homogeneousComponent_of_mem_ne hf (Ne.symm hk)

/-- A homogeneous pure tensor has exactly its summed degree in the completion. -/
theorem component_tensorCompletionMap_tmul {f g : SymmetricFunction R} {i j : ℕ}
    (hf : IsHomogeneous f i) (hg : IsHomogeneous g j) (n : ℕ) :
    CompletedTensor.component R (tensorCompletionMap R (f ⊗ₜ[R] g)) n =
      if n = i + j then f ⊗ₜ[R] g else 0 := by
  classical
  rw [tensorCompletionMap_tmul, component_completedTensorProduct]
  simp only [component_completionEmbedding]
  have hfi (k : ℕ) : homogeneousComponent k f = if k = i then f else 0 := by
    split_ifs with hk
    · subst k; exact homogeneousComponent_of_mem hf
    · exact homogeneousComponent_of_mem_ne hf (Ne.symm hk)
  have hgj (k : ℕ) : homogeneousComponent k g = if k = j then g else 0 := by
    split_ifs with hk
    · subst k; exact homogeneousComponent_of_mem hg
    · exact homogeneousComponent_of_mem_ne hg (Ne.symm hk)
  by_cases hn : n = i + j
  · subst n
    rw [ite_eq_left rfl]
    rw [Finset.sum_eq_single (i, j)]
    · rw [homogeneousComponent_of_mem hf, homogeneousComponent_of_mem hg]
    · intro ab hab hne
      have hneq : ab.1 ≠ i ∨ ab.2 ≠ j := by
        by_contra h
        simp only [not_or, not_not] at h
        exact hne (Prod.ext h.1 h.2)
      rcases hneq with hi | hj
      · rw [hfi, ite_eq_right hi, TensorProduct.zero_tmul]
      · rw [hgj, ite_eq_right hj, TensorProduct.tmul_zero]
    · simp
  · rw [ite_eq_right hn]
    apply Finset.sum_eq_zero
    intro ab hab
    by_cases hi : ab.1 = i
    · have hj : ab.2 ≠ j := by
        intro hj
        exact hn ((Finset.mem_antidiagonal.mp hab).symm.trans (by rw [hi, hj]))
      rw [hgj, ite_eq_right hj, TensorProduct.tmul_zero]
    · rw [hfi, ite_eq_right hi, TensorProduct.zero_tmul]

/-- The bounded tensor map places each total-homogeneous tensor in its own degree. -/
theorem component_tensorCompletionMap_of_mem
    {z : SymmetricFunction R ⊗[R] SymmetricFunction R} {d : ℕ}
    (hz : z ∈ tensorDegree R d) (n : ℕ) :
    CompletedTensor.component R (tensorCompletionMap R z) n =
      if n = d then z else 0 := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, j, f, g, hij, hf, hg, rfl⟩ := hz
    rw [component_tensorCompletionMap_tmul R hf hg, hij]
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [map_add, CompletedTensor.component_add, ihx, ihy]
    split_ifs <;> simp
  | smul r x hx ih =>
    rw [map_smul, CompletedTensor.component_smul, ih]
    split_ifs <;> simp

/-- The completed coproduct agrees with the original Hopf coproduct on bounded functions. -/
theorem completedCoproduct_embedding (f : SymmetricFunction R) :
    completedCoproduct R (completionEmbedding R f) =
      tensorCompletionMap R (comultiplication f) := by
  have he : (completedCoproduct R).comp (completionEmbedding R) =
      (tensorCompletionMap R).comp comultiplication := by
    apply algHom_ext
    intro i
    apply GradedCompletion.ext
    intro n
    change CompletedTensor.component R (completedCoproduct R (completionEmbedding R (e i))) n =
      CompletedTensor.component R (tensorCompletionMap R (comultiplication (e i))) n
    rw [component_completedCoproduct, component_completionEmbedding,
      component_tensorCompletionMap_of_mem R
        (comultiplication_mem_tensorDegree (isHomogeneous_e i))]
    split_ifs with hn
    · subst n; rw [homogeneousComponent_of_mem (isHomogeneous_e i)]
    · rw [homogeneousComponent_of_mem_ne (isHomogeneous_e i) (Ne.symm hn), map_zero]
  exact AlgHom.congr_fun he f

end SymmetricFunction
