import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.Ring

/-! # Units encoding total exterior powers of line elements -/

noncomputable section

namespace LambdaRing.Polynomial

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The total exterior power of a line element, as an actual formal-series unit. -/
def lineUnit (a : A) : (PowerSeries A)ˣ where
  val := 1 + PowerSeries.C a * PowerSeries.X
  inv := PowerSeries.invOfUnit (1 + PowerSeries.C a * PowerSeries.X) 1
  val_inv := PowerSeries.mul_invOfUnit _ 1 (by simp)
  inv_val := PowerSeries.invOfUnit_mul _ 1 (by simp)

@[simp] theorem coe_lineUnit (a : A) :
    (lineUnit a : PowerSeries A) = 1 + PowerSeries.C a * PowerSeries.X := rfl

@[simp] theorem lineUnit_zero : lineUnit (0 : A) = 1 := by
  apply Units.ext
  simp

@[simp] theorem constantCoeff_lineUnit (a : A) :
    PowerSeries.constantCoeff (lineUnit a : PowerSeries A) = 1 := by simp

@[simp] theorem coeff_one_lineUnit (a : A) :
    PowerSeries.coeff 1 (lineUnit a : PowerSeries A) = a := by simp

/-- Mapping a line unit maps its line element. -/
@[simp] theorem map_lineUnit (φ : A →+* B) (a : A) :
    Units.map (PowerSeries.map φ).toMonoidHom (lineUnit a) = lineUnit (φ a) := by
  apply Units.ext
  simp

/-- Normalization is preserved under inverses. -/
theorem constantCoeff_unit_inv (u : (PowerSeries A)ˣ)
    (hu : PowerSeries.constantCoeff (u : PowerSeries A) = 1) :
    PowerSeries.constantCoeff (↑u⁻¹ : PowerSeries A) = 1 := by
  have h := congrArg PowerSeries.constantCoeff
    (show (u : PowerSeries A) * (↑u⁻¹ : PowerSeries A) = 1 from u.val_inv)
  rw [map_mul, hu, one_mul, map_one] at h
  exact h

/-- Normalization is preserved under every signed power. -/
theorem constantCoeff_unit_zpow (u : (PowerSeries A)ˣ)
    (hu : PowerSeries.constantCoeff (u : PowerSeries A) = 1) (z : ℤ) :
    PowerSeries.constantCoeff (↑(u ^ z) : PowerSeries A) = 1 := by
  have h : Units.map PowerSeries.constantCoeff.toMonoidHom u = 1 := Units.ext hu
  have hz := congrArg (fun v : Aˣ => (v : A)) (map_zpow
    (Units.map PowerSeries.constantCoeff.toMonoidHom) u z)
  change PowerSeries.constantCoeff (↑(u ^ z) : PowerSeries A) =
    ↑((Units.map PowerSeries.constantCoeff.toMonoidHom u) ^ z) at hz
  rw [h, one_zpow, Units.val_one] at hz
  exact hz

/-- The linear coefficient of the inverse of a normalized unit changes sign. -/
theorem coeff_one_unit_inv (u : (PowerSeries A)ˣ)
    (hu : PowerSeries.constantCoeff (u : PowerSeries A) = 1) :
    PowerSeries.coeff 1 (↑u⁻¹ : PowerSeries A) = -PowerSeries.coeff 1 (u : PowerSeries A) := by
  have h := congrArg (PowerSeries.coeff 1)
    (show (u : PowerSeries A) * (↑u⁻¹ : PowerSeries A) = 1 from u.val_inv)
  rw [PowerSeries.coeff_one_mul] at h
  simp only [hu, constantCoeff_unit_inv u hu, mul_one, PowerSeries.coeff_one,
    one_ne_zero, ↓reduceIte] at h
  exact eq_neg_of_add_eq_zero_right h

/-- The linear coefficient of a signed power is the signed multiple. -/
theorem coeff_one_unit_zpow (u : (PowerSeries A)ˣ)
    (hu : PowerSeries.constantCoeff (u : PowerSeries A) = 1) (z : ℤ) :
    PowerSeries.coeff 1 (↑(u ^ z) : PowerSeries A) =
      z • PowerSeries.coeff 1 (u : PowerSeries A) := by
  cases z with
  | ofNat n =>
    simp [PowerSeries.coeff_one_pow, hu]
  | negSucc n =>
    simp [zpow_negSucc, ← inv_pow, PowerSeries.coeff_one_pow,
      constantCoeff_unit_inv u hu, coeff_one_unit_inv u hu, zsmul_eq_mul]
    ring

/-- Negative one line multiplicity gives the geometric series with alternating signs. -/
theorem coe_lineUnit_inv (a : A) : (↑(lineUnit a)⁻¹ : PowerSeries A) =
    PowerSeries.mk (fun n => (-a) ^ n) := by
  apply Units.inv_eq_of_mul_eq_one_left
  have h := congrArg (PowerSeries.rescale (-a))
    (PowerSeries.mk_one_mul_one_sub_eq_one A)
  simpa [PowerSeries.rescale_mk, PowerSeries.rescale_X] using h

@[simp] theorem coeff_lineUnit_inv (a : A) (n : ℕ) :
    PowerSeries.coeff n (↑(lineUnit a)⁻¹ : PowerSeries A) = (-a) ^ n := by
  rw [coe_lineUnit_inv, PowerSeries.coeff_mk]

/-- Every negative multiplicity has an integral binomial coefficient formula. -/
theorem coeff_lineUnit_negSucc (a : A) (r n : ℕ) :
    PowerSeries.coeff n (↑(lineUnit a ^ (-((r + 1 : ℕ) : ℤ))) : PowerSeries A) =
      (-a) ^ n * (Nat.choose (r + n) r : A) := by
  have h : (↑(lineUnit a)⁻¹ : PowerSeries A) =
      PowerSeries.rescale (-a) (PowerSeries.mk 1) := by
    rw [coe_lineUnit_inv, PowerSeries.rescale_mk]
    congr 1
    funext k
    simp
  rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, h, ← map_pow,
    PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.coeff_rescale,
    PowerSeries.coeff_mk]

end LambdaRing.Polynomial
