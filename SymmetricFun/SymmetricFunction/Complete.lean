module

public import SymmetricFun.SymmetricFunction.Basic

/-!
# Complete homogeneous symmetric functions

The degree-`n` complete homogeneous symmetric function has coefficient one on
every monomial of total degree `n`, and zero elsewhere.
-/

@[expose] public section
noncomputable section

namespace MvPowerSeries

variable (σ R : Type*) [CommSemiring R]

/-- The degree-`n` complete homogeneous symmetric function as a power series. -/
def hsymmMvPowerSeries (n : ℕ) : MvPowerSeries σ R :=
  fun c ↦ if c.degree = n then 1 else 0

end MvPowerSeries
