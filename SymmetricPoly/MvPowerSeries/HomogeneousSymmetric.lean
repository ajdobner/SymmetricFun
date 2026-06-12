import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Operations

import SymmetricPoly.MvPowerSeries.Homogeneous
import SymmetricPoly.MvPowerSeries.Symmetric
import SymmetricPoly.Partition

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


-- /-- The algebra of symmetric functions. (Note: `σ` may be finite, in which case this is actually
-- just the algebra of symmetric polynomials.) -/
-- abbrev SymmetricFunction (σ R : Type*) [CommSemiring R] :=
--   MvPowerSeries.symmetricFunctionSubalgebra σ R

-- namespace SymmetricFunction
-- variable (σ R : Type*) [CommSemiring R]

-- def symmetricHomogeneousSubmodule (n : ℕ) :
--   Submodule R (SymmetricFunction σ R) :=
--   (MvPowerSeries.homogeneousSubmodule σ R n).comap (SymmetricFunction σ R).val.toLinearMap

-- /-- The monomial symmetric function bundled as an element of `SymmetricFunction`. -/
-- def msymm (μ : Partition) : SymmetricFunction σ R :=
--   ⟨MvPowerSeries.msymmMvPowerSeries σ R μ,
--   MvPowerSeries.msymmMvPowerSeries_mem_symmetricFunctionSubalgebra σ R μ⟩

-- @[simp, norm_cast]
-- lemma coe_msymm (μ : Partition) :
--     ↑(msymm σ R μ) = MvPowerSeries.msymmMvPowerSeries σ R μ :=
--   rfl

-- def esymm (n : ℕ) : SymmetricFunction σ R := sorry

-- end SymmetricFunction
