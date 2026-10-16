import SymmetricFunctions.Completion.Graded
import SymmetricFunctions.Realization.PowerSeries

/-! # Degree completion and inclusive truncations

An element is a product of weighted homogeneous components, with no uniform
bound. Truncation through D retains the components numbered 0 through D.
-/

noncomputable section

namespace SymmetricFunction

open SymmetricFunctions

variable (R : Type*) [CommRing R]

/-- Completed symmetric functions, with degree n equal to symmetric-function degree n. -/
abbrev DegreeCompletion := GradedCompletion (homogeneousSubmodule R)

namespace DegreeCompletion

/-- The nth homogeneous component as a bounded symmetric function. -/
abbrev component (F : DegreeCompletion R) (n : ℕ) : SymmetricFunction R :=
  GradedCompletion.component (homogeneousSubmodule R) F n

@[ext] theorem ext {F G : DegreeCompletion R} (h : ∀ n, component R F n = component R G n) :
    F = G := GradedCompletion.ext _ h

theorem component_homogeneous (F : DegreeCompletion R) (n : ℕ) :
    IsHomogeneous (component R F n) n := GradedCompletion.component_mem _ F n

theorem component_mul (F G : DegreeCompletion R) (n : ℕ) :
    component R (F * G) n = ∑ ij ∈ Finset.antidiagonal n,
      component R F ij.1 * component R G ij.2 := GradedCompletion.component_mul _ F G n

@[simp] theorem component_zero (n : ℕ) : component R 0 n = 0 :=
  GradedCompletion.component_zero _ n

@[simp] theorem component_one (n : ℕ) : component R 1 n = if n = 0 then 1 else 0 :=
  GradedCompletion.component_one _ n

@[simp] theorem component_add (F G : DegreeCompletion R) (n : ℕ) :
    component R (F + G) n = component R F n + component R G n :=
  GradedCompletion.component_add _ F G n

@[simp] theorem component_algebraMap (r : R) (n : ℕ) :
    component R (algebraMap R (DegreeCompletion R) r) n =
      if n = 0 then algebraMap R (SymmetricFunction R) r else 0 :=
  GradedCompletion.component_algebraMap _ r n

end DegreeCompletion

/-- The product coefficient formula in the original direct-sum grading. -/
theorem homogeneousComponent_mul (f g : SymmetricFunction R) (n : ℕ) :
    homogeneousComponent n (f * g) = ∑ ij ∈ Finset.antidiagonal n,
      homogeneousComponent ij.1 f * homogeneousComponent ij.2 g := by
  simp only [homogeneousComponent_eq_decompose]
  rw [map_mul, DirectSum.coe_mul_apply_eq_sum_antidiagonal]

/-- The homogeneous family of a bounded function. -/
def completionFamily (f : SymmetricFunction R) : DegreeCompletion R := fun n => decompose R f n

/-- Bounded functions embed by their actual homogeneous projections. -/
def completionEmbedding : SymmetricFunction R →ₐ[R] DegreeCompletion R where
  toFun := completionFamily R
  map_zero' := by
    apply DegreeCompletion.ext
    intro n
    change homogeneousComponent n (0 : SymmetricFunction R) = _
    simp [DegreeCompletion.component]
  map_one' := by
    apply DegreeCompletion.ext
    intro n
    change homogeneousComponent n (1 : SymmetricFunction R) = _
    rw [DegreeCompletion.component_one]
    split_ifs with hn
    · subst n; exact homogeneousComponent_of_mem isHomogeneous_one
    · exact homogeneousComponent_of_mem_ne isHomogeneous_one (Ne.symm hn)
  map_add' f g := by
    apply DegreeCompletion.ext
    intro n
    change homogeneousComponent n (f + g) = _
    rw [map_add, DegreeCompletion.component_add]
    rfl
  map_mul' f g := by
    apply DegreeCompletion.ext
    intro n
    change homogeneousComponent n (f * g) = _
    rw [DegreeCompletion.component_mul, homogeneousComponent_mul]
    rfl
  commutes' r := by
    apply DegreeCompletion.ext
    intro n
    change homogeneousComponent n (algebraMap R (SymmetricFunction R) r) = _
    rw [DegreeCompletion.component_algebraMap]
    split_ifs with hn
    · subst n; exact homogeneousComponent_of_mem (isHomogeneous_algebraMap r)
    · exact homogeneousComponent_of_mem_ne (isHomogeneous_algebraMap r) (Ne.symm hn)

@[simp] theorem component_completionEmbedding (f : SymmetricFunction R) (n : ℕ) :
    DegreeCompletion.component R (completionEmbedding R f) n = homogeneousComponent n f := rfl

theorem completionEmbedding_injective : Function.Injective (completionEmbedding R) := by
  intro f g h
  apply (decompose R).injective
  ext n
  exact congrArg (fun F : DegreeCompletion R => DegreeCompletion.component R F n) h

namespace DegreeCompletion

/-- Inclusive finite truncation, taking values in the bounded ring. -/
def truncate (D : ℕ) (F : DegreeCompletion R) : SymmetricFunction R :=
  ∑ n ∈ Finset.range (D + 1), component R F n

/-- Every truncated component is either the original one or zero. -/
theorem homogeneousComponent_truncate (D n : ℕ) (F : DegreeCompletion R) :
    homogeneousComponent n (truncate R D F) = if n ≤ D then component R F n else 0 := by
  classical
  rw [truncate, map_sum]
  have he (i : ℕ) : homogeneousComponent n (component R F i) =
      if i = n then component R F n else 0 := by
    by_cases h : i = n
    · subst i; rw [ite_eq_left rfl]; exact homogeneousComponent_of_mem (component_homogeneous R F n)
    · rw [ite_eq_right h]; exact homogeneousComponent_of_mem_ne (component_homogeneous R F i) h
  simp only [he, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff]

theorem truncate_mem_degreeLE (D : ℕ) (F : DegreeCompletion R) :
    truncate R D F ∈ degreeLE R D := by
  rw [mem_degreeLE_iff]
  intro n hn
  rw [homogeneousComponent_truncate, ite_eq_right (not_le.mpr hn)]

/-- Equality of completed components through D is equivalent to equality of truncations. -/
theorem truncate_eq_iff (D : ℕ) (F G : DegreeCompletion R) :
    truncate R D F = truncate R D G ↔ ∀ n ≤ D, component R F n = component R G n := by
  constructor
  · intro h n hn
    simpa only [homogeneousComponent_truncate, ite_eq_left hn] using
      congrArg (homogeneousComponent n) h
  · intro h
    apply Finset.sum_congr rfl
    intro n hn
    exact h n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))

/-- Finite truncation commutes with multiplication after truncating the output too. -/
theorem truncate_mul (D : ℕ) (F G : DegreeCompletion R) :
    truncate R D (F * G) = truncate R D
      (completionEmbedding R (truncate R D F * truncate R D G)) := by
  apply (truncate_eq_iff R D _ _).mpr
  intro n hn
  rw [component_completionEmbedding, component_mul, homogeneousComponent_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hsum := Finset.mem_antidiagonal.mp hij
  rw [homogeneousComponent_truncate, homogeneousComponent_truncate,
    ite_eq_left (by omega : ij.1 ≤ D), ite_eq_left (by omega : ij.2 ≤ D)]

/-- Truncating an already truncated function changes only the cutoff. -/
theorem truncate_truncate (D E : ℕ) (F : DegreeCompletion R) :
    truncate R D (completionEmbedding R (truncate R E F)) = truncate R (min D E) F := by
  apply (decompose R).injective
  ext n
  change homogeneousComponent n _ = homogeneousComponent n _
  simp only [homogeneousComponent_truncate, component_completionEmbedding]
  by_cases hD : n ≤ D <;> by_cases hE : n ≤ E <;> simp [hD, hE]

/-- A truncation at any genuine degree bound recovers a bounded function. -/
theorem truncate_completionEmbedding_of_degreeLE (D : ℕ) {f : SymmetricFunction R}
    (hf : f ∈ degreeLE R D) : truncate R D (completionEmbedding R f) = f := by
  apply (decompose R).injective
  ext n
  change homogeneousComponent n _ = homogeneousComponent n f
  rw [homogeneousComponent_truncate, component_completionEmbedding]
  split_ifs with hn
  · rfl
  · exact ((mem_degreeLE_iff.mp hf) n (Nat.lt_of_not_ge hn)).symm

end DegreeCompletion
end SymmetricFunction
