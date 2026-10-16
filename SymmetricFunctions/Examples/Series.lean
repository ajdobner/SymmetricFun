import SymmetricFunctions.Realization.PowerSeries

/-! # Uniform bounds, actual alphabet coefficients, and finite restrictions -/

noncomputable section
namespace SymmetricFunction.Examples

open SymmetricFunctions SymmetricFunctions.Series
variable {R : Type*} [CommRing R]
attribute [local irreducible] SymmetricFunction

example : SymmetricFunction (ZMod 2) ≃ₐ[ZMod 2] BoundedSymmetricSeries (ZMod 2) :=
  boundedSeriesEquiv (ZMod 2)

example : SymmetricFunction PUnit ≃ₐ[PUnit] BoundedSymmetricSeries PUnit :=
  boundedSeriesEquiv PUnit

example (F : BoundedSymmetricSeries R) :
    ∃ D, ∀ a : ℕ →₀ ℕ, MvPowerSeries.coeff a F.val ≠ 0 → a.degree ≤ D := F.property.2

example (i : ℕ) :
    MvPowerSeries.coeff (Finsupp.single i 2)
      (toSeries R (mPart (Nat.Partition.indiscrete 2))) = 1 := by
  classical
  simp [exponentParts]

example (f : SymmetricFunction R) :
    finiteRestriction R 0 (toSeries R f) = ((rho R 0 f).val : MvPowerSeries (Fin 0) R) := by
  simp

example (N : ℕ) :
    finiteRestriction R N (toSeries R (h 2)) =
      (MvPolynomial.hsymm (Fin N) R 2 : MvPowerSeries (Fin N) R) :=
  finiteRestriction_toSeries_h R N 2

example : (toSeries R (e 2)).IsHomogeneous 2 :=
  isHomogeneous_toSeries R (isHomogeneous_e 2)

example (f : SymmetricFunction R) : (boundedSeriesEquiv R).symm (boundedSeriesEquiv R f) = f := by
  simp

end SymmetricFunction.Examples
