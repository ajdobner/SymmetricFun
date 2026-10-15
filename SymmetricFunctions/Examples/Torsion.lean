import SymmetricFunctions.Lambda.Universal
import LambdaRing.Transport
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Data.ZMod.Basic

/-! # A proved special lambda target with nonzero additive torsion

The target is the square-zero extension of the integers by Z/2. Its special
structure descends from the constructed one-variable integer polynomial ring.
-/

noncomputable section

namespace SymmetricFunction.Examples.Torsion

open MvPolynomial LambdaRing.Polynomial

/-- The right integer action is the same canonical integer scalar action. -/
instance oppositeIntModule : Module ℤᵐᵒᵖ (ZMod 2) :=
  Module.compHom (ZMod 2) (RingEquiv.toOpposite ℤ).symm.toRingHom

instance centralIntScalar : IsCentralScalar ℤ (ZMod 2) where
  op_smul_eq_smul _ _ := rfl

/-- A characteristic-zero ring with a nonzero ideal of additive order two. -/
abbrev Target := TrivSqZeroExt ℤ (ZMod 2)

/-- The nonzero square-zero element of order two. -/
def epsilon : Target := TrivSqZeroExt.inr 1

@[simp] theorem epsilon_sq : epsilon ^ 2 = 0 := by
  rw [pow_two]
  exact TrivSqZeroExt.inr_mul_inr ℤ _ _

/-- Square-zero line elements add by multiplying their linear series. -/
private theorem lineUnit_add_of_mul_eq_zero {A : Type*} [CommRing A]
    (a b : A) (hab : a * b = 0) : lineUnit (a+b) = lineUnit a * lineUnit b := by
  apply Units.ext
  simp only [coe_lineUnit, Units.val_mul, map_add, add_mul]
  have hz : (PowerSeries.C a * PowerSeries.X) * (PowerSeries.C b * PowerSeries.X) = 0 := by
    calc
      _ = PowerSeries.C (a*b) * PowerSeries.X^2 := by rw [map_mul]; ring
      _ = 0 := by rw [hab, map_zero, zero_mul]
  rw [one_mul, mul_add, mul_one, hz]
  ring

/-- The square-zero coordinate contributes one linear factor. -/
def linearUnitHom : ZMod 2 →+ Additive ((PowerSeries Target)ˣ) where
  toFun b := Additive.ofMul (lineUnit (TrivSqZeroExt.inr b : Target))
  map_zero' := by simp
  map_add' b c := by
    change lineUnit (TrivSqZeroExt.inr (b+c) : Target) = _
    rw [TrivSqZeroExt.inr_add]
    exact lineUnit_add_of_mul_eq_zero _ _ (TrivSqZeroExt.inr_mul_inr ℤ b c)

/-- Total exterior powers on the square-zero extension, before any class is claimed. -/
def targetTotal (x : Target) : (PowerSeries Target)ˣ :=
  lineUnit (1 : Target) ^ x.fst * (linearUnitHom x.snd).toMul

@[simp] theorem targetTotal_zero : targetTotal (0 : Target) = 1 := by simp [targetTotal]

theorem targetTotal_add (x y : Target) : targetTotal (x+y) = targetTotal x * targetTotal y := by
  simp only [targetTotal, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add, zpow_add,
    toMul_add]
  ac_rfl

def targetTotalHom : Target →+ Additive ((PowerSeries Target)ˣ) where
  toFun x := Additive.ofMul (targetTotal x)
  map_zero' := targetTotal_zero
  map_add' := targetTotal_add

theorem targetTotal_zsmul (z : ℤ) (x : Target) : targetTotal (z • x) = targetTotal x ^ z :=
  map_zsmul targetTotalHom z x

@[simp] theorem targetTotal_one : targetTotal (1 : Target) = lineUnit 1 := by
  simp [targetTotal]

@[simp] theorem targetTotal_epsilon : targetTotal epsilon = lineUnit epsilon := by
  simp [targetTotal, epsilon, linearUnitHom]

theorem targetTotal_epsilon_pow (k : ℕ) : targetTotal (epsilon ^ k) = lineUnit (epsilon ^ k) := by
  cases k with
  | zero => simp
  | succ k =>
    cases k with
    | zero => simp
    | succ k =>
      have h : epsilon ^ (k+2) = 0 := by rw [pow_add, epsilon_sq, mul_zero]
      simp only [h, targetTotal_zero, lineUnit_zero]

/-- The canonical surjection sends the sole polynomial variable to epsilon. -/
def projection : MvPolynomial Unit ℤ →+* Target :=
  eval₂Hom (Int.castRingHom Target) (fun _ => epsilon)

@[simp] theorem projection_C (a : ℤ) : projection (C a) = (a : Target) :=
  eval₂Hom_C _ _ _

@[simp] theorem projection_X : projection (X ()) = epsilon := eval₂Hom_X' _ _ _

theorem projection_surjective : Function.Surjective projection := by
  intro x
  refine ⟨C x.fst + C (x.snd.val : ℤ) * X (), ?_⟩
  rw [map_add, map_mul, projection_C, projection_C, projection_X]
  apply TrivSqZeroExt.ext
  · simp [epsilon]
  · simp only [ZMod.natCast_val, ZMod.intCast_cast, TrivSqZeroExt.snd_add,
      TrivSqZeroExt.snd_intCast, TrivSqZeroExt.snd_mul, zsmul_eq_mul,
      op_smul_eq_smul, zero_add]
    rw [ZMod.cast_eq_val, TrivSqZeroExt.fst_natCast]
    simp [epsilon]

@[simp] theorem projection_monomial_one (m : Unit →₀ ℕ) :
    projection (monomial m 1) = epsilon ^ m () := by
  rw [projection, eval₂Hom_monomial]
  simp only [map_one, one_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp

/-- The total-series formula is compatible with every signed polynomial representative. -/
theorem projection_totalUnit (f : MvPolynomial Unit ℤ) :
    Units.map (PowerSeries.map projection).toMonoidHom (totalUnit f) =
      targetTotal (projection f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial m a =>
    have hm : monomial m a = a • monomial m (1 : ℤ) := by rw [← map_zsmul]; simp
    rw [totalUnit_monomial, map_zpow, map_lineUnit, hm, map_zsmul, targetTotal_zsmul,
      projection_monomial_one, targetTotal_epsilon_pow]
  | add f g hf hg => rw [totalUnit_add, map_mul, hf, hg, map_add, targetTotal_add]

/-- The exterior-power coefficient on the torsion target. -/
def targetOperation (n : ℕ) (x : Target) : Target :=
  PowerSeries.coeff n (targetTotal x : PowerSeries Target)

theorem projection_operation (n : ℕ) (f : MvPolynomial Unit ℤ) :
    projection (operation n f) = targetOperation n (projection f) :=
  congrArg (fun u : (PowerSeries Target)ˣ => PowerSeries.coeff n (u : PowerSeries Target))
    (projection_totalUnit f)

instance : PreLambdaRing Target :=
  PreLambdaRing.ofSurjective projection projection_surjective targetOperation projection_operation

instance : SpecialLambdaRing Target :=
  SpecialLambdaRing.ofSurjective projection projection_surjective projection_operation

/-- The polynomial projection is an actual preserving morphism to a special ring with torsion. -/
def projectionLambdaHom : LambdaRingHom (MvPolynomial Unit ℤ) Target :=
  { projection with map_lambda' := projection_operation }

theorem epsilon_ne_zero : epsilon ≠ 0 := by
  intro h
  have he := congrArg TrivSqZeroExt.snd h
  simp [epsilon] at he

theorem two_smul_epsilon : (2 : ℤ) • epsilon = 0 := by
  apply TrivSqZeroExt.ext
  · simp [epsilon]
  · change (2 : ℤ) • (1 : ZMod 2) = 0
    decide

/-- A torsion-valued evaluation furnished by the proved universal property. -/
def evaluation : LambdaRingHom (SymmetricFunction ℤ) Target := lambdaEval epsilon

@[simp] theorem evaluation_e_one : evaluation (e 1) = epsilon := lambdaEval_e_one _

@[simp] theorem evaluation_e_two : evaluation (e 2) = 0 := by
  rw [evaluation, lambdaEval_e]
  change targetOperation 2 epsilon = 0
  simp [targetOperation, targetTotal_epsilon]

example : evaluation (e 1) ≠ 0 := by rw [evaluation_e_one]; exact epsilon_ne_zero

example : (2 : ℤ) • evaluation (e 1) = 0 := by rw [evaluation_e_one]; exact two_smul_epsilon

end SymmetricFunction.Examples.Torsion
