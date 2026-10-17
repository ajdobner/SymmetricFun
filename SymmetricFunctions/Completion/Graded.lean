import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.Algebra.TransferInstance

/-! # Products of graded pieces with finite convolution

The auxiliary PowerSeries model is used to prove the algebra laws. The carrier
is the product of the pieces, and multiplication is finite in every degree.
-/

noncomputable section

namespace SymmetricFunctions

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (G : ℕ → Submodule R A) [SetLike.GradedMonoid G]

/-- The product of graded pieces; it is not given pointwise multiplication. -/
def GradedCompletion := ∀ n : ℕ, G n

namespace GradedCompletion

/-- Auxiliary series whose nth coefficient belongs to the nth graded piece. -/
def seriesSubalgebra : Subalgebra R (PowerSeries A) where
  carrier := {F | ∀ n, PowerSeries.coeff n F ∈ G n}
  add_mem' hF hH n := by simpa using (G n).add_mem (hF n) (hH n)
  mul_mem' hF hH n := by
    rw [PowerSeries.coeff_mul]
    apply (G n).sum_mem
    intro ij hij
    have h := SetLike.GradedMul.mul_mem (hF ij.1) (hH ij.2)
    simpa only [Finset.mem_antidiagonal.mp hij] using h
  algebraMap_mem' r n := by
    rw [PowerSeries.algebraMap_apply]
    rw [PowerSeries.coeff_C]
    split_ifs with hn
    · subst n
      simpa only [Algebra.smul_def, mul_one] using
        (G 0).smul_mem r (SetLike.GradedOne.one_mem : (1 : A) ∈ G 0)
    · exact (G n).zero_mem

/-- A product of pieces is exactly a series with homogeneous coefficients. -/
def seriesEquiv : GradedCompletion G ≃ seriesSubalgebra G where
  toFun F := ⟨PowerSeries.mk (fun n => (F n).val), fun n => by
    rw [PowerSeries.coeff_mk]; exact (F n).property⟩
  invFun F n := ⟨PowerSeries.coeff n F.val, F.property n⟩
  left_inv F := by
    funext n
    apply Subtype.ext
    change PowerSeries.coeff n (PowerSeries.mk (fun i => (F i).val)) = (F n).val
    exact PowerSeries.coeff_mk n _
  right_inv F := by
    apply Subtype.ext
    ext n
    change PowerSeries.coeff n (PowerSeries.mk (fun i => PowerSeries.coeff i F.val)) = _
    exact PowerSeries.coeff_mk n _

instance : CommRing (GradedCompletion G) := (seriesEquiv G).commRing
instance : Algebra R (GradedCompletion G) := (seriesEquiv G).algebra R

/-- Algebraic packaging of the auxiliary coefficient model. -/
def seriesAlgEquiv : GradedCompletion G ≃ₐ[R] seriesSubalgebra G :=
  (seriesEquiv G).algEquiv R

/-- The degree-n component as an element of the ambient graded algebra. -/
def component (F : GradedCompletion G) (n : ℕ) : A := (F n).val

omit [SetLike.GradedMonoid G] in
theorem component_mem (F : GradedCompletion G) (n : ℕ) : component G F n ∈ G n :=
  (F n).property

omit [SetLike.GradedMonoid G] in
@[ext] theorem ext {F H : GradedCompletion G}
    (h : ∀ n, component G F n = component G H n) : F = H := by
  funext n
  exact Subtype.ext (h n)

/-- The auxiliary series map is injective and preserves the convolution algebra. -/
def toPowerSeries : GradedCompletion G →ₐ[R] PowerSeries A :=
  (seriesSubalgebra G).val.comp (seriesAlgEquiv G).toAlgHom

@[simp] theorem coeff_toPowerSeries (F : GradedCompletion G) (n : ℕ) :
    PowerSeries.coeff n (toPowerSeries G F) = component G F n := by
  change PowerSeries.coeff n (PowerSeries.mk (fun i => (F i).val)) = (F n).val
  exact PowerSeries.coeff_mk n _

theorem toPowerSeries_injective : Function.Injective (toPowerSeries G) := by
  intro F H h
  apply ext G
  intro n
  simpa only [coeff_toPowerSeries] using congrArg (PowerSeries.coeff n) h

@[simp] theorem component_zero (n : ℕ) : component G 0 n = 0 := by
  rw [← coeff_toPowerSeries, map_zero, map_zero]

@[simp] theorem component_add (F H : GradedCompletion G) (n : ℕ) :
    component G (F + H) n = component G F n + component G H n := by
  simp only [← coeff_toPowerSeries, map_add]

@[simp] theorem component_smul (r : R) (F : GradedCompletion G) (n : ℕ) :
    component G (r • F) n = r • component G F n := by
  simp only [← coeff_toPowerSeries, map_smul, PowerSeries.coeff_smul]

@[simp] theorem component_algebraMap (r : R) (n : ℕ) :
    component G (algebraMap R (GradedCompletion G) r) n =
      if n = 0 then algebraMap R A r else 0 := by
  rw [← coeff_toPowerSeries, AlgHom.commutes]
  rw [PowerSeries.algebraMap_apply, PowerSeries.coeff_C]

@[simp] theorem component_one (n : ℕ) :
    component G 1 n = if n = 0 then 1 else 0 := by
  rw [← coeff_toPowerSeries, map_one, PowerSeries.coeff_one]

/-- Finite antidiagonal convolution, counting the degrees in both factors. -/
theorem component_mul (F H : GradedCompletion G) (n : ℕ) :
    component G (F * H) n = ∑ ij ∈ Finset.antidiagonal n,
      component G F ij.1 * component G H ij.2 := by
  simp only [← coeff_toPowerSeries, map_mul, PowerSeries.coeff_mul]

private def mapFamily {B : Type*} [CommRing B] [Algebra R B]
    (H : ℕ → Submodule R B) (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ G n → φ a ∈ H n) (F : GradedCompletion G) :
    GradedCompletion H := fun n => ⟨φ (component G F n), hφ n _ (component_mem G F n)⟩

/-- A degree-preserving algebra map extends componentwise to the products. -/
def map {B : Type*} [CommRing B] [Algebra R B]
    (H : ℕ → Submodule R B) [SetLike.GradedMonoid H] (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ G n → φ a ∈ H n) : GradedCompletion G →ₐ[R] GradedCompletion H where
  toFun := mapFamily G H φ hφ
  map_zero' := by
    apply ext H
    intro n
    change φ (component G 0 n) = component H 0 n
    simp
  map_one' := by
    apply ext H
    intro n
    change φ (component G 1 n) = component H 1 n
    simp [component_one, apply_ite φ]
  map_add' F K := by
    apply ext H
    intro n
    change φ (component G (F + K) n) = _
    rw [component_add, map_add, component_add]
    rfl
  map_mul' F K := by
    apply ext H
    intro n
    change φ (component G (F * K) n) = _
    rw [component_mul, map_sum, component_mul]
    apply Finset.sum_congr rfl
    intro ij _
    exact map_mul φ _ _
  commutes' r := by
    apply ext H
    intro n
    change φ (component G (algebraMap R (GradedCompletion G) r) n) = _
    rw [component_algebraMap, component_algebraMap]
    simp [apply_ite φ]

@[simp] theorem component_map {B : Type*} [CommRing B] [Algebra R B]
    (H : ℕ → Submodule R B) [SetLike.GradedMonoid H] (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ G n → φ a ∈ H n) (F : GradedCompletion G) (n : ℕ) :
    component H (map G H φ hφ F) n = φ (component G F n) := rfl

end GradedCompletion
end SymmetricFunctions
