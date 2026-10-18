module

public import Mathlib.RingTheory.GradedAlgebra.AlgHom

/-!
# Equivalences of graded algebras

`GradedAlgEquiv R 𝒜 ℬ`, written `𝒜 ≃ₐᵍ[R] ℬ`, is an algebra equivalence that
preserves membership in each homogeneous component in both directions.
It implements `EquivLike`, `AlgEquivClass`, and `GradedEquivLike`.

The basic operations only require families of submodules. When the families are
gradings, an equivalence also gives a `GradedAlgHom` and commutes with homogeneous
projections. A bijective graded algebra homomorphism can be promoted using
`GradedAlgEquiv.ofBijective`: injectivity and compatibility with projections imply
that the inverse preserves the grading.
-/

@[expose] public section

/-- An algebra equivalence preserving each homogeneous component in both directions. -/
structure GradedAlgEquiv (R : Type*) {A B ι : Type*}
    [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B) extends A ≃ₐ[R] B where
  /-- The equivalence preserves and reflects membership in each component. -/
  map_mem_iff' {i : ι} {x : A} : toAlgEquiv x ∈ ℬ i ↔ x ∈ 𝒜 i

@[inherit_doc]
notation:25 𝒜 " ≃ₐᵍ[" R "] " ℬ => GradedAlgEquiv R 𝒜 ℬ

namespace GradedAlgEquiv

variable {R A B C D ι : Type*}
  [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
  {𝒜 : ι → Submodule R A} {ℬ : ι → Submodule R B}
  {𝒞 : ι → Submodule R C} {𝒟 : ι → Submodule R D}

@[macro_inline]
instance : EquivLike (𝒜 ≃ₐᵍ[R] ℬ) A B where
  coe e := e.toAlgEquiv
  inv e := e.toAlgEquiv.symm
  left_inv e := e.toAlgEquiv.left_inv
  right_inv e := e.toAlgEquiv.right_inv
  coe_injective' e f h _ := by
    have hef : e.toAlgEquiv = f.toAlgEquiv := DFunLike.coe_injective h
    cases e
    cases f
    cases hef
    rfl

instance : AlgEquivClass (𝒜 ≃ₐᵍ[R] ℬ) R A B where
  map_add e := e.toAlgEquiv.map_add
  map_mul e := e.toAlgEquiv.map_mul
  commutes e := e.toAlgEquiv.commutes

instance : GradedEquivLike (𝒜 ≃ₐᵍ[R] ℬ) 𝒜 ℬ where
  map_mem_iff e := e.map_mem_iff'

attribute [coe] toAlgEquiv

instance : CoeOut (𝒜 ≃ₐᵍ[R] ℬ) (A ≃ₐ[R] B) := ⟨toAlgEquiv⟩

initialize_simps_projections GradedAlgEquiv (toFun → apply, invFun → symm_apply)

@[simp]
theorem coe_toAlgEquiv (e : 𝒜 ≃ₐᵍ[R] ℬ) : ⇑e.toAlgEquiv = e := rfl

@[ext]
theorem ext {e f : 𝒜 ≃ₐᵍ[R] ℬ} (h : ∀ x, e x = f x) : e = f :=
  DFunLike.ext _ _ h

theorem toAlgEquiv_injective :
    Function.Injective (toAlgEquiv : (𝒜 ≃ₐᵍ[R] ℬ) → A ≃ₐ[R] B) :=
  fun _ _ h => ext fun x => DFunLike.congr_fun h x

@[simp]
theorem map_mem_iff (e : 𝒜 ≃ₐᵍ[R] ℬ) {i : ι} {x : A} :
    e x ∈ ℬ i ↔ x ∈ 𝒜 i :=
  Graded.map_mem_iff e

theorem map_mem (e : 𝒜 ≃ₐᵍ[R] ℬ) {i : ι} {x : A} (hx : x ∈ 𝒜 i) :
    e x ∈ ℬ i :=
  Graded.map_mem e hx

theorem injective (e : 𝒜 ≃ₐᵍ[R] ℬ) : Function.Injective e :=
  e.toAlgEquiv.injective

theorem surjective (e : 𝒜 ≃ₐᵍ[R] ℬ) : Function.Surjective e :=
  e.toAlgEquiv.surjective

theorem bijective (e : 𝒜 ≃ₐᵍ[R] ℬ) : Function.Bijective e :=
  e.toAlgEquiv.bijective

/-- The identity as a graded algebra equivalence. -/
@[refl]
def refl (R : Type*) {A ι : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (𝒜 : ι → Submodule R A) : 𝒜 ≃ₐᵍ[R] 𝒜 :=
  { AlgEquiv.refl with map_mem_iff' := Iff.rfl }

@[simp]
theorem refl_apply (x : A) : refl R 𝒜 x = x := rfl

@[simp]
theorem refl_toAlgEquiv : (refl R 𝒜).toAlgEquiv = AlgEquiv.refl := rfl

/-- The inverse of a graded algebra equivalence. -/
@[symm]
def symm (e : 𝒜 ≃ₐᵍ[R] ℬ) : ℬ ≃ₐᵍ[R] 𝒜 :=
  { e.toAlgEquiv.symm with
    map_mem_iff' := fun {i y} => by
      simpa only [AlgEquiv.apply_symm_apply] using
        (e.map_mem_iff' (i := i) (x := e.toAlgEquiv.symm y)).symm }

@[simp]
theorem symm_toAlgEquiv (e : 𝒜 ≃ₐᵍ[R] ℬ) :
    e.symm.toAlgEquiv = e.toAlgEquiv.symm := rfl

@[simp]
theorem symm_symm (e : 𝒜 ≃ₐᵍ[R] ℬ) : e.symm.symm = e := rfl

@[simp]
theorem apply_symm_apply (e : 𝒜 ≃ₐᵍ[R] ℬ) (y : B) : e (e.symm y) = y :=
  e.toAlgEquiv.apply_symm_apply y

@[simp]
theorem symm_apply_apply (e : 𝒜 ≃ₐᵍ[R] ℬ) (x : A) : e.symm (e x) = x :=
  e.toAlgEquiv.symm_apply_apply x

/-- Composition of graded algebra equivalences, applying the first argument first. -/
@[trans]
def trans (e : 𝒜 ≃ₐᵍ[R] ℬ) (f : ℬ ≃ₐᵍ[R] 𝒞) : 𝒜 ≃ₐᵍ[R] 𝒞 :=
  { e.toAlgEquiv.trans f.toAlgEquiv with
    map_mem_iff' := f.map_mem_iff.trans e.map_mem_iff }

@[simp]
theorem trans_apply (e : 𝒜 ≃ₐᵍ[R] ℬ) (f : ℬ ≃ₐᵍ[R] 𝒞) (x : A) :
    (e.trans f) x = f (e x) := rfl

@[simp]
theorem trans_toAlgEquiv (e : 𝒜 ≃ₐᵍ[R] ℬ) (f : ℬ ≃ₐᵍ[R] 𝒞) :
    (e.trans f).toAlgEquiv = e.toAlgEquiv.trans f.toAlgEquiv := rfl

@[simp]
theorem refl_trans (e : 𝒜 ≃ₐᵍ[R] ℬ) : (refl R 𝒜).trans e = e := by ext; rfl

@[simp]
theorem trans_refl (e : 𝒜 ≃ₐᵍ[R] ℬ) : e.trans (refl R ℬ) = e := by ext; rfl

theorem trans_assoc (e : 𝒜 ≃ₐᵍ[R] ℬ) (f : ℬ ≃ₐᵍ[R] 𝒞) (g : 𝒞 ≃ₐᵍ[R] 𝒟) :
    (e.trans f).trans g = e.trans (f.trans g) := by ext; rfl

@[simp]
theorem self_trans_symm (e : 𝒜 ≃ₐᵍ[R] ℬ) : e.trans e.symm = refl R 𝒜 := by ext; simp

@[simp]
theorem symm_trans_self (e : 𝒜 ≃ₐᵍ[R] ℬ) : e.symm.trans e = refl R ℬ := by ext; simp

@[simp]
theorem trans_symm (e : 𝒜 ≃ₐᵍ[R] ℬ) (f : ℬ ≃ₐᵍ[R] 𝒞) :
    (e.trans f).symm = f.symm.trans e.symm := by ext; rfl

/-- Restrict a graded algebra equivalence to a linear equivalence on one component. -/
def gradedLinearEquiv (e : 𝒜 ≃ₐᵍ[R] ℬ) (i : ι) : 𝒜 i ≃ₗ[R] ℬ i :=
  { Graded.equiv e i with
    map_add' x y := Subtype.ext (map_add e (x : A) (y : A))
    map_smul' r x := Subtype.ext (map_smul e r (x : A)) }

@[simp]
theorem coe_gradedLinearEquiv_apply (e : 𝒜 ≃ₐᵍ[R] ℬ) (i : ι) (x : 𝒜 i) :
    (e.gradedLinearEquiv i x : B) = e x := rfl

@[simp]
theorem gradedLinearEquiv_refl (i : ι) :
    (refl R 𝒜).gradedLinearEquiv i = LinearEquiv.refl R (𝒜 i) := by ext; rfl

@[simp]
theorem gradedLinearEquiv_symm (e : 𝒜 ≃ₐᵍ[R] ℬ) (i : ι) :
    e.symm.gradedLinearEquiv i = (e.gradedLinearEquiv i).symm := by ext; rfl

@[simp]
theorem gradedLinearEquiv_trans (e : 𝒜 ≃ₐᵍ[R] ℬ) (f : ℬ ≃ₐᵍ[R] 𝒞) (i : ι) :
    (e.trans f).gradedLinearEquiv i =
      (e.gradedLinearEquiv i).trans (f.gradedLinearEquiv i) := by ext; rfl

section GradedAlgebra

variable [DecidableEq ι] [AddMonoid ι]
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]

/-- Forget the inverse of a graded algebra equivalence. -/
@[coe]
def toGradedAlgHom (e : 𝒜 ≃ₐᵍ[R] ℬ) : 𝒜 →ₐᵍ[R] ℬ :=
  { e.toAlgEquiv.toAlgHom with map_mem := e.map_mem }

instance : CoeOut (𝒜 ≃ₐᵍ[R] ℬ) (𝒜 →ₐᵍ[R] ℬ) := ⟨toGradedAlgHom⟩

@[simp]
theorem coe_toGradedAlgHom (e : 𝒜 ≃ₐᵍ[R] ℬ) : ⇑e.toGradedAlgHom = e := rfl

@[simp]
theorem toGradedAlgHom_toAlgHom (e : 𝒜 ≃ₐᵍ[R] ℬ) :
    e.toGradedAlgHom.toAlgHom = e.toAlgEquiv.toAlgHom := rfl

@[simp]
theorem refl_toGradedAlgHom :
    (refl R 𝒜).toGradedAlgHom = GradedAlgHom.id R 𝒜 := rfl

@[simp]
theorem trans_toGradedAlgHom (e : 𝒜 ≃ₐᵍ[R] ℬ) (f : ℬ ≃ₐᵍ[R] 𝒞) :
    (e.trans f).toGradedAlgHom = f.toGradedAlgHom.comp e.toGradedAlgHom := rfl

/-- A graded algebra equivalence commutes with projection onto a homogeneous component. -/
@[simp]
theorem map_proj (e : 𝒜 ≃ₐᵍ[R] ℬ) (i : ι) (x : A) :
    e (GradedAlgebra.proj 𝒜 i x) = GradedAlgebra.proj ℬ i (e x) :=
  map_directSumDecompose 𝒜 ℬ e

end GradedAlgebra

end GradedAlgEquiv

namespace GradedAlgHom

variable {R A B ι : Type*}
  [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [DecidableEq ι] [AddMonoid ι]
  {𝒜 : ι → Submodule R A} {ℬ : ι → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- An injective graded algebra homomorphism reflects membership in homogeneous components. -/
theorem map_mem_iff_of_injective (f : 𝒜 →ₐᵍ[R] ℬ) (hf : Function.Injective f)
    {i : ι} {x : A} : f x ∈ ℬ i ↔ x ∈ 𝒜 i := by
  refine ⟨fun hx => ?_, Graded.map_mem f⟩
  have h : (DirectSum.decompose 𝒜 x i : A) = x := hf (by
    rw [map_directSumDecompose 𝒜 ℬ f, DirectSum.decompose_of_mem_same ℬ hx])
  exact h ▸ (DirectSum.decompose 𝒜 x i).property

/-- A graded algebra homomorphism commutes with projection onto a homogeneous component. -/
@[simp]
theorem map_proj (f : 𝒜 →ₐᵍ[R] ℬ) (i : ι) (x : A) :
    f (GradedAlgebra.proj 𝒜 i x) = GradedAlgebra.proj ℬ i (f x) :=
  map_directSumDecompose 𝒜 ℬ f

end GradedAlgHom

namespace GradedAlgEquiv

variable {R A B ι : Type*}
  [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [DecidableEq ι] [AddMonoid ι]
  {𝒜 : ι → Submodule R A} {ℬ : ι → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- Promote a bijective graded algebra homomorphism to a graded algebra equivalence. -/
noncomputable def ofBijective (f : 𝒜 →ₐᵍ[R] ℬ) (hf : Function.Bijective f) :
    𝒜 ≃ₐᵍ[R] ℬ :=
  { AlgEquiv.ofBijective f.toAlgHom hf with
    map_mem_iff' := f.map_mem_iff_of_injective hf.1 }

@[simp]
theorem ofBijective_toAlgEquiv (f : 𝒜 →ₐᵍ[R] ℬ) (hf : Function.Bijective f) :
    (ofBijective f hf).toAlgEquiv = AlgEquiv.ofBijective f.toAlgHom hf := rfl

@[simp]
theorem ofBijective_toGradedAlgHom (f : 𝒜 →ₐᵍ[R] ℬ) (hf : Function.Bijective f) :
    (ofBijective f hf).toGradedAlgHom = f := by ext; rfl

@[simp]
theorem ofBijective_apply (f : 𝒜 →ₐᵍ[R] ℬ) (hf : Function.Bijective f) (x : A) :
    ofBijective f hf x = f x := rfl

end GradedAlgEquiv
