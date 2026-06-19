import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Operations

import SymmetricPoly.MvPowerSeries.Homogeneous
import SymmetricPoly.MvPowerSeries.Symmetric

noncomputable section

namespace MvPowerSeries

/-- The submodule of homogeneous `MvPowerSeries`s of degree `n`. -/
def homogeneousSymmetricSubmodule (σ R : Type*) [CommSemiring R] (n : ℕ) :
    Submodule R (MvPowerSeries σ R) :=
  homogeneousSubmodule σ R n ⊓ (symmetricSubalgebra σ R).toSubmodule

@[simp]
theorem mem_homogeneousSymmetricSubmodule (n : ℕ) [CommSemiring R] (p : MvPowerSeries σ R) :
    p ∈ homogeneousSymmetricSubmodule σ R n ↔ p.IsHomogeneous n ∧ IsSymmetric p := by
  apply Submodule.mem_inf

instance HomogeneousSymmetric.gradedMonoid (σ R : Type*) [CommSemiring R] :
  SetLike.GradedMonoid (homogeneousSymmetricSubmodule σ R) where
  one_mem := by
    rw [mem_homogeneousSymmetricSubmodule]
    constructor
    · exact isHomogeneous_one
    · exact isSymmetric_one
  mul_mem _ _ _ _ := by
    rw [mem_homogeneousSymmetricSubmodule]
    rintro ⟨ha, hs⟩ ⟨hb, ht⟩
    constructor
    · exact IsHomogeneous.mul ha hb
    · apply (symmetricSubalgebra σ R).mul_mem
      · exact hs
      · exact ht

def symmetricFunctionSubalgebra (σ R : Type*) [CommSemiring R] : Subalgebra R (MvPowerSeries σ R) :=
  boundedDegreeSubalgebra σ R ⊓ symmetricSubalgebra σ R

@[simp]
theorem mem_symmetricFunctionSubalgebra [CommSemiring R] (p : MvPowerSeries σ R) :
    p ∈ symmetricFunctionSubalgebra σ R ↔ p.HasBoundedDegree ∧ p.IsSymmetric := by
  change p ∈ boundedDegreeSubalgebra σ R ∧ p ∈ symmetricSubalgebra σ R ↔
    p.HasBoundedDegree ∧ p.IsSymmetric
  simp

end MvPowerSeries
