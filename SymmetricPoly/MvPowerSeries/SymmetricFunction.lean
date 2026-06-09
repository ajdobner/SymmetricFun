import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Operations

import SymmetricPoly.MvPowerSeries.SymmetricAction
import SymmetricPoly.MvPowerSeries.Homogeneous
import SymmetricPoly.Partition

noncomputable section

namespace MvPowerSeries

section SymmetricFunction

def symmetricFunctionSubalgebra (σ R : Type*) [CommSemiring R] : Subalgebra R (MvPowerSeries σ R) :=
  boundedDegreeSubalgebra σ R ⊓ symmetricSubalgebra σ R

section MonomialSymmetric
variable (σ R : Type*) [CommSemiring R] (μ : Partition)

def msymmMvPowerSeries : MvPowerSeries σ R :=
  fun (m : σ →₀ ℕ) =>
    if m.toPartition = μ then 1 else 0

theorem msymmMvPowerSeries_isHomogeneous : IsHomogeneous (msymmMvPowerSeries σ R μ) |μ| := by
  sorry

@[simp]
lemma coeff_msymmMvPowerSeries {σ R : Type*} [CommSemiring R]
    (μ : Partition) (m : σ →₀ ℕ) :
  coeff m (msymmMvPowerSeries σ R μ) = if m.toPartition = μ then 1 else 0 := rfl

theorem msymmMvPowerSeries_isSymmetric : IsSymmetric (msymmMvPowerSeries σ R μ) := by
  intro e; ext m; simp

theorem msymmMvPowerSeries_mem_symmetricFunctionSubalgebra :
  msymmMvPowerSeries σ R μ ∈ symmetricFunctionSubalgebra σ R := by
  constructor
  · apply mem_boundedDegreeSubalgebra_of_isHomogeneous
    exact msymmMvPowerSeries_isHomogeneous σ R μ
  · exact msymmMvPowerSeries_isSymmetric σ R μ

end MonomialSymmetric

section ElementarySymmetric
variable (σ R : Type*) [CommSemiring R]

def esymmMvPowerSeries (n : ℕ) : MvPowerSeries σ R :=
  fun c ↦ if c.support.card = n ∧ (∀ i ∈ c.support, c i = 1) then 1 else 0

end ElementarySymmetric

section HomogeneousSymmetric
variable (σ R : Type*) [CommSemiring R]

def hsymmMvPowerSeries (n : ℕ) : MvPowerSeries σ R :=
  fun c ↦ if c.degree = n then 1 else 0

end HomogeneousSymmetric

end SymmetricFunction

end MvPowerSeries

/-- The algebra of symmetric functions. (Note: `σ` may be finite, in which case this is actually
  just the algebra of symmetric polynomials.) -/
abbrev SymmetricFunction (σ R : Type*) [CommSemiring R] :=
  MvPowerSeries.symmetricFunctionSubalgebra σ R

namespace SymmetricFunction
variable (σ R : Type*) [CommSemiring R]

def symmetricHomogeneousSubmodule (n : ℕ) :
  Submodule R (SymmetricFunction σ R) :=
  (MvPowerSeries.homogeneousSubmodule σ R n).comap (SymmetricFunction σ R).val.toLinearMap

/-- The monomial symmetric function bundled as an element of `SymmetricFunction`. -/
def msymm (μ : Partition) : SymmetricFunction σ R :=
  ⟨MvPowerSeries.msymmMvPowerSeries σ R μ,
  MvPowerSeries.msymmMvPowerSeries_mem_symmetricFunctionSubalgebra σ R μ⟩

@[simp, norm_cast]
lemma coe_msymm (μ : Partition) :
    ↑(msymm σ R μ) = MvPowerSeries.msymmMvPowerSeries σ R μ :=
  rfl

def esymm (n : ℕ) : SymmetricFunction σ R := sorry

end SymmetricFunction
