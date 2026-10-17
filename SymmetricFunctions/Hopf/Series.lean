import SymmetricFunctions.Hopf.Basic
import Mathlib.RingTheory.PowerSeries.Derivative

/-! # Integral generating series and the complete coproduct -/

namespace SymmetricFunction

noncomputable section

open scoped TensorProduct

variable {R : Type*} [CommRing R]

/-- A formal bookkeeping series with bounded symmetric-function coefficients. -/
def elementaryGeneratingSeries : PowerSeries (SymmetricFunction R) := PowerSeries.mk e

/-- Each coefficient is a bounded complete symmetric function. -/
def completeGeneratingSeries : PowerSeries (SymmetricFunction R) := PowerSeries.mk h

@[simp] theorem coeff_elementaryGeneratingSeries (n : ℕ) :
    PowerSeries.coeff n (elementaryGeneratingSeries (R := R)) = e n :=
  PowerSeries.coeff_mk _ _

@[simp] theorem coeff_completeGeneratingSeries (n : ℕ) :
    PowerSeries.coeff n (completeGeneratingSeries (R := R)) = h n :=
  PowerSeries.coeff_mk _ _

theorem elementary_complete_series :
    PowerSeries.rescale (-1) (elementaryGeneratingSeries (R := R)) *
      completeGeneratingSeries = 1 := by
  ext n
  simpa [PowerSeries.coeff_mul, Algebra.smul_def, mul_assoc] using
    e_h_convolution (R := R) n

/-- The two tensor inclusions give the multiplication law for the elementary series. -/
theorem comultiplication_elementarySeries :
    PowerSeries.map comultiplication.toRingHom (elementaryGeneratingSeries (R := R)) =
      PowerSeries.map (Algebra.TensorProduct.includeLeft :
        SymmetricFunction R →ₐ[R] SymmetricFunction R ⊗[R] SymmetricFunction R).toRingHom
        elementaryGeneratingSeries *
      PowerSeries.map (Algebra.TensorProduct.includeRight :
        SymmetricFunction R →ₐ[R] SymmetricFunction R ⊗[R] SymmetricFunction R).toRingHom
        elementaryGeneratingSeries := by
  ext n
  simp [PowerSeries.coeff_mul, comultiplication_e]

theorem comultiplication_completeSeries :
    PowerSeries.map comultiplication.toRingHom (completeGeneratingSeries (R := R)) =
      PowerSeries.map (Algebra.TensorProduct.includeLeft :
        SymmetricFunction R →ₐ[R] SymmetricFunction R ⊗[R] SymmetricFunction R).toRingHom
        completeGeneratingSeries *
      PowerSeries.map (Algebra.TensorProduct.includeRight :
        SymmetricFunction R →ₐ[R] SymmetricFunction R ⊗[R] SymmetricFunction R).toRingHom
        completeGeneratingSeries := by
  let L := (Algebra.TensorProduct.includeLeft :
    SymmetricFunction R →ₐ[R] SymmetricFunction R ⊗[R] SymmetricFunction R).toRingHom
  let Q := (Algebra.TensorProduct.includeRight :
    SymmetricFunction R →ₐ[R] SymmetricFunction R ⊗[R] SymmetricFunction R).toRingHom
  let E := elementaryGeneratingSeries (R := R)
  let H := completeGeneratingSeries (R := R)
  let M := PowerSeries.map (comultiplication (R := R)).toRingHom
  have hl := congrArg (PowerSeries.map L) (elementary_complete_series (R := R))
  have hr := congrArg (PowerSeries.map Q) (elementary_complete_series (R := R))
  have hm := congrArg M (elementary_complete_series (R := R))
  have rescale_map (φ : SymmetricFunction R →+*
      SymmetricFunction R ⊗[R] SymmetricFunction R) :
      PowerSeries.map φ (PowerSeries.rescale (-1) E) =
        PowerSeries.rescale (-1) (PowerSeries.map φ E) := by
    simpa using (PowerSeries.rescale_map φ (-1) E).symm
  simp only [map_mul, map_one] at hl hr hm
  rw [rescale_map] at hl hr
  change M (PowerSeries.rescale (-1) E) * M H = 1 at hm
  have he : M (PowerSeries.rescale (-1) E) =
      PowerSeries.rescale (-1) (PowerSeries.map L E) *
        PowerSeries.rescale (-1) (PowerSeries.map Q E) := by
    rw [rescale_map, comultiplication_elementarySeries, map_mul]
  rw [he] at hm
  have hi : (PowerSeries.map L H * PowerSeries.map Q H) *
      (PowerSeries.rescale (-1) (PowerSeries.map L E) *
        PowerSeries.rescale (-1) (PowerSeries.map Q E)) = 1 := by
    calc
      _ = (PowerSeries.rescale (-1) (PowerSeries.map L E) * PowerSeries.map L H) *
          (PowerSeries.rescale (-1) (PowerSeries.map Q E) * PowerSeries.map Q H) := by ring
      _ = 1 := by rw [hl, hr, one_mul]
  exact (left_inv_eq_right_inv hi hm).symm

/-- Complete functions have the same antidiagonal coproduct as elementary functions. -/
@[simp] theorem comultiplication_h (n : ℕ) :
    comultiplication (h (R := R) n) =
      ∑ ij ∈ Finset.antidiagonal n, h ij.1 ⊗ₜ[R] h ij.2 := by
  have hc := congrArg (PowerSeries.coeff n) (comultiplication_completeSeries (R := R))
  simpa [PowerSeries.coeff_mul] using hc

end

end SymmetricFunction
