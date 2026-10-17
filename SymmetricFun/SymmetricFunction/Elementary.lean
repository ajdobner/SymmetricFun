module

public import SymmetricFun.SymmetricFunction.Basic

/-!
# Elementary symmetric functions

The degree-`n` elementary symmetric function has coefficient one on the squarefree
monomials supported on exactly `n` variables, and zero elsewhere.
-/

@[expose] public section
noncomputable section

namespace MvPowerSeries

variable (σ R : Type*) [CommSemiring R]

/-- The degree-`n` elementary symmetric function as a power series. -/
def esymmMvPowerSeries (n : ℕ) : MvPowerSeries σ R :=
  fun c ↦ if c.support.card = n ∧ (∀ i ∈ c.support, c i = 1) then 1 else 0

end MvPowerSeries
