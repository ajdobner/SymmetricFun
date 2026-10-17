import SymmetricFunctions.Compatibility.Upstream
import SymmetricFunctions.Omega
import SymmetricFunctions.Lambda.Structure
import Mathlib.Data.ZMod.Basic

/-! # Using proved extension operations with the native power-series API -/
noncomputable section
namespace SymmetricFunction.Examples

-- The elementary/complete involution can be applied to Alex's native generators
-- through the equivalence, with the result his existing complete function.
example {R : Type*} [CommRing R] (i : ℕ+) :
    upstreamEquiv ℕ R (omega ((upstreamEquiv ℕ R).symm
      (MvPowerSeries.esymmGraded ℕ R i : MvPowerSeries.symmetricFunctionSubalgebra ℕ R))) =
      (MvPowerSeries.hsymmGraded ℕ R i : MvPowerSeries.symmetricFunctionSubalgebra ℕ R) := by
  rw [← upstreamEquiv_e ℕ R i, AlgEquiv.symm_apply_apply, omega_e, upstreamEquiv_h]

-- Integral exterior powers recover the native elementary family, including n = 0.
example (n : ℕ) :
    (upstreamEquiv ℕ ℤ (LambdaRing.lambda n (e 1)) : MvPowerSeries ℕ ℤ) =
      MvPowerSeries.esymm ℕ ℤ n := by
  rw [lambda_e_one, coe_upstreamEquiv_e]

-- The bridge is not restricted to characteristic zero or to nontrivial rings.
example : (upstreamEquiv ℕ (ZMod 6) (h 2) : MvPowerSeries ℕ (ZMod 6)) =
    MvPowerSeries.hsymm ℕ (ZMod 6) 2 := coe_upstreamEquiv_h _ _

example (f : SymmetricFunction (ZMod 1)) (n : ℕ) :
    upstreamEquiv ℕ (ZMod 1) f ∈ MvPowerSeries.symmetricFunctionGrading ℕ (ZMod 1) n ↔
      IsHomogeneous f n := upstreamEquiv_mem_grading_iff _ _ _ _

-- The fundamental theorem also connects alphabets of arbitrary infinite cardinality.
example (σ R : Type*) [Infinite σ] [CommRing R]
    (f : MvPowerSeries.symmetricFunctionSubalgebra σ R) :
    upstreamEquiv σ R ((upstreamEquiv σ R).symm f) = f :=
  (upstreamEquiv σ R).apply_symm_apply f

end SymmetricFunction.Examples
