import LambdaRing.Hom
import LambdaRing.Polynomial.Density

/-! # Integral closure principles for preserving exterior powers

No characteristic or torsion hypotheses are used. Formal series encode the
addition law solely to establish preservation under additive inverses.
-/

noncomputable section

namespace LambdaRing

variable {A B : Type*} [CommRing A] [PreLambdaRing A] [CommRing B] [PreLambdaRing B]

/-- Preservation of all exterior powers at one specified element. -/
def PreservesAt (φ : A →+* B) (a : A) : Prop := ∀ n, φ (lambda n a) = lambda n (φ a)

/-- The total exterior-power series of an element of any pre-lambda ring. -/
def totalSeries (a : A) : PowerSeries A := PowerSeries.mk (fun n => lambda n a)

@[simp] theorem coeff_totalSeries (a : A) (n : ℕ) :
    PowerSeries.coeff n (totalSeries a) = lambda n a := PowerSeries.coeff_mk _ _

theorem totalSeries_add (a b : A) : totalSeries (a+b) = totalSeries a * totalSeries b := by
  ext n
  simp only [coeff_totalSeries, PowerSeries.coeff_mul, lambda_add]

@[simp] theorem totalSeries_zero : totalSeries (0 : A) = 1 := by
  ext n
  simp only [coeff_totalSeries, lambda_zero_input, PowerSeries.coeff_one]

theorem totalSeries_mul_neg (a : A) : totalSeries a * totalSeries (-a) = 1 := by
  rw [← totalSeries_add, add_neg_cancel, totalSeries_zero]

theorem preservesAt_iff_map_totalSeries (φ : A →+* B) (a : A) :
    PreservesAt φ a ↔ PowerSeries.map φ (totalSeries a) = totalSeries (φ a) := by
  rw [PowerSeries.ext_iff]
  simp only [PowerSeries.coeff_map, coeff_totalSeries, PreservesAt]

@[simp] theorem preservesAt_zero (φ : A →+* B) : PreservesAt φ 0 := by
  intro n
  simp only [lambda_zero_input, map_zero]
  split <;> simp

theorem PreservesAt.add {φ : A →+* B} {a b : A}
    (ha : PreservesAt φ a) (hb : PreservesAt φ b) : PreservesAt φ (a+b) := by
  dsimp only [PreservesAt] at ha hb
  intro n
  simp only [lambda_add, map_add, map_sum, map_mul, ha, hb]

theorem PreservesAt.neg {φ : A →+* B} {a : A} (ha : PreservesAt φ a) :
    PreservesAt φ (-a) := by
  apply (preservesAt_iff_map_totalSeries φ (-a)).mpr
  rw [map_neg]
  have h := congrArg (PowerSeries.map φ) (totalSeries_mul_neg a)
  rw [map_mul, map_one, (preservesAt_iff_map_totalSeries φ a).mp ha] at h
  have ht : totalSeries (-φ a) * totalSeries (φ a) = 1 := by
    rw [mul_comm, totalSeries_mul_neg]
  exact (left_inv_eq_right_inv ht h).symm

variable [SpecialLambdaRing A] [SpecialLambdaRing B]

@[simp] theorem preservesAt_one (φ : A →+* B) : PreservesAt φ 1 := by
  intro n
  rw [lambda_unit, map_one, lambda_unit]
  split <;> simp

theorem PreservesAt.mul {φ : A →+* B} {a b : A}
    (ha : PreservesAt φ a) (hb : PreservesAt φ b) : PreservesAt φ (a*b) := by
  dsimp only [PreservesAt] at ha hb
  intro n
  rw [lambda_mul, map_mul, lambda_mul, Polynomial.map_int_aeval_sum φ]
  simp only [ha, hb]

/-- The locus on which a ring map preserves every exterior power is a subring. -/
def preservingSubring (φ : A →+* B) : Subring A where
  carrier := {a | PreservesAt φ a}
  zero_mem' := preservesAt_zero φ
  one_mem' := preservesAt_one φ
  add_mem' := PreservesAt.add
  neg_mem' := PreservesAt.neg
  mul_mem' := PreservesAt.mul

@[simp] theorem mem_preservingSubring (φ : A →+* B) (a : A) :
    a ∈ preservingSubring φ ↔ PreservesAt φ a := Iff.rfl

/-- The iteration identity gives closure under every exterior-power operation. -/
theorem PreservesAt.lambda {φ : A →+* B} {a : A} (ha : PreservesAt φ a) (m : ℕ) :
    PreservesAt φ (lambda m a) := by
  dsimp only [PreservesAt] at ha
  intro n
  rw [lambda_iterate, Polynomial.map_int_aeval φ, ha m, lambda_iterate]
  simp only [ha]

end LambdaRing
