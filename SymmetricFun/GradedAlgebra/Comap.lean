module

public import Mathlib.RingTheory.GradedAlgebra.AlgHom

/-!
# Restricting a grading along an injective algebra homomorphism

An injective algebra homomorphism whose range is closed under homogeneous
projections pulls the grading back to its domain. The pieces are defined by
`Submodule.comap`, and the homomorphism commutes with the resulting projections.
-/

@[expose] public section
noncomputable section

namespace GradedAlgebra

variable {ι R A B : Type*} [DecidableEq ι] [AddMonoid ι]
  [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  (ℬ : ι → Submodule R B) [GradedAlgebra ℬ] (f : A →ₐ[R] B)

private theorem proj_map_coeLinearMap_comap (i : ι)
    (x : DirectSum ι fun j => (ℬ j).comap f.toLinearMap) :
    proj ℬ i (f (DirectSum.coeLinearMap (fun j => (ℬ j).comap f.toLinearMap) x)) =
      f (x i) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j x =>
    rw [DirectSum.coeLinearMap_of]
    by_cases h : j = i
    · subst j
      rw [DirectSum.of_eq_same]
      exact DirectSum.decompose_of_mem_same ℬ x.property
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), Submodule.coe_zero, map_zero]
      exact DirectSum.decompose_of_mem_ne ℬ x.property h
  | add x y hx hy =>
    simpa only [map_add, DirectSum.add_apply, Submodule.coe_add] using
      congrArg₂ (· + ·) hx hy

/-- A grading restricts along an injective algebra homomorphism with homogeneous range. -/
theorem isInternal_comap (hf : Function.Injective f)
    (h : DirectSum.SetLike.IsHomogeneous ℬ f.range) :
    DirectSum.IsInternal (fun i => (ℬ i).comap f.toLinearMap) := by
  classical
  change Function.Bijective (DirectSum.coeLinearMap (fun i => (ℬ i).comap f.toLinearMap))
  constructor
  · intro x y hxy
    ext i : 1
    apply Subtype.ext
    apply hf
    rw [← proj_map_coeLinearMap_comap, ← proj_map_coeLinearMap_comap, hxy]
  · intro a
    have hproj (i : ι) : ∃ b : A, f b = proj ℬ i (f a) :=
      h i ⟨a, rfl⟩
    choose c hc using hproj
    have hc_mem (i : ι) : c i ∈ (ℬ i).comap f.toLinearMap := by
      change f (c i) ∈ ℬ i
      rw [hc]
      exact (DirectSum.decompose ℬ (f a) i).property
    refine ⟨∑ i ∈ (DirectSum.decompose ℬ (f a)).support,
      DirectSum.of (fun j => (ℬ j).comap f.toLinearMap) i ⟨c i, hc_mem i⟩, ?_⟩
    apply hf
    simp only [map_sum, DirectSum.coeLinearMap_of]
    simp_rw [hc]
    exact DirectSum.sum_support_decompose ℬ (f a)

/-- Pull back a grading along an injective algebra homomorphism with homogeneous range. -/
@[instance_reducible]
def comap (hf : Function.Injective f)
    (h : DirectSum.SetLike.IsHomogeneous ℬ f.range) :
    GradedAlgebra (fun i => (ℬ i).comap f.toLinearMap) := by
  letI : SetLike.GradedMonoid (fun i => (ℬ i).comap f.toLinearMap) :=
    { one_mem := by
        change f 1 ∈ ℬ 0
        rw [map_one]
        exact SetLike.one_mem_graded ℬ
      mul_mem := by
        intro i j a b ha hb
        change f (a * b) ∈ ℬ (i + j)
        rw [map_mul]
        exact SetLike.mul_mem_graded ha hb }
  exact (isInternal_comap ℬ f hf h).gradedAlgebra

/-- The homomorphism into the ambient algebra commutes with the pulled-back projections. -/
theorem map_proj_comap [GradedAlgebra (fun i => (ℬ i).comap f.toLinearMap)]
    (i : ι) (a : A) :
    f (proj (fun j => (ℬ j).comap f.toLinearMap) i a) = proj ℬ i (f a) := by
  let g : (fun j => (ℬ j).comap f.toLinearMap) →ₐᵍ[R] ℬ :=
    { f with map_mem := fun hx => hx }
  exact map_directSumDecompose (fun j => (ℬ j).comap f.toLinearMap) ℬ g

end GradedAlgebra
