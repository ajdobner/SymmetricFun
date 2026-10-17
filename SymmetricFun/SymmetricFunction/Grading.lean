module

public import SymmetricFun.GradedAlgebra.Comap
public import SymmetricFun.SymmetricFunction.Basic

/-!
# The grading of symmetric functions

The grading of bounded-degree power series restricts to symmetric functions:
homogeneous projections commute with permutations, so they preserve symmetry.
The pieces are defined directly inside the symmetric-function algebra using its
inclusion into power series. They are definitionally the pullbacks of the pieces
of the bounded-degree algebra.

The `symmetricFunctionGrading` namespace provides a constructor from a homogeneous
symmetric series, accessors for its properties, and extensionality through the
underlying power series.
-/

@[expose] public section
noncomputable section

namespace MvPowerSeries

variable (σ R : Type*) [CommSemiring R]

/-- The degree `n` piece, viewed as a submodule of the symmetric-function algebra. -/
def symmetricFunctionGrading (n : ℕ) :
    Submodule R (symmetricFunctionSubalgebra σ R) :=
  (homogeneousSubmodule σ R n).comap
    (symmetricFunctionSubalgebra σ R).val.toLinearMap

@[simp]
theorem mem_symmetricFunctionGrading (n : ℕ) (f : symmetricFunctionSubalgebra σ R) :
    f ∈ symmetricFunctionGrading σ R n ↔ IsHomogeneous (f : MvPowerSeries σ R) n :=
  Iff.rfl

namespace symmetricFunctionGrading

variable {σ R} {n : ℕ}

/-- Bundle a homogeneous symmetric power series as an element of its graded piece. -/
def mk (f : MvPowerSeries σ R) (hf : IsHomogeneous f n) (hs : IsSymmetric f) :
    symmetricFunctionGrading σ R n :=
  ⟨⟨f, mem_symmetricFunctionSubalgebra_of_isHomogeneous hf hs⟩, hf⟩

@[simp]
theorem coe_mk (f : MvPowerSeries σ R) (hf : IsHomogeneous f n) (hs : IsSymmetric f) :
    (mk f hf hs : MvPowerSeries σ R) = f :=
  rfl

/-- The underlying power series has the degree of its graded piece. -/
theorem isHomogeneous (f : symmetricFunctionGrading σ R n) :
    IsHomogeneous (f : MvPowerSeries σ R) n :=
  f.property

/-- The underlying power series of an element of a symmetric graded piece is symmetric. -/
theorem isSymmetric (f : symmetricFunctionGrading σ R n) :
    IsSymmetric (f : MvPowerSeries σ R) :=
  symmetricFunctionSubalgebra.isSymmetric (f : symmetricFunctionSubalgebra σ R)

theorem hasBoundedDegree (f : symmetricFunctionGrading σ R n) :
    HasBoundedDegree (f : MvPowerSeries σ R) :=
  symmetricFunctionSubalgebra.hasBoundedDegree (f : symmetricFunctionSubalgebra σ R)

@[simp]
theorem mk_coe (f : symmetricFunctionGrading σ R n) :
    mk (f : MvPowerSeries σ R) (isHomogeneous f) (isSymmetric f) = f :=
  rfl

/-- Equality in a graded piece can be checked on the underlying power series. -/
@[ext]
theorem ext {f g : symmetricFunctionGrading σ R n}
    (h : (f : MvPowerSeries σ R) = (g : MvPowerSeries σ R)) : f = g :=
  Subtype.ext (Subtype.ext h)

end symmetricFunctionGrading

theorem symmetricFunctionGrading_eq_comap (n : ℕ) :
    symmetricFunctionGrading σ R n =
      (boundedDegreeGrading σ R n).comap (symmetricFunctionToBoundedDegree σ R).toLinearMap :=
  rfl

/-- Symmetric functions form a homogeneous subalgebra of the bounded-degree algebra. -/
theorem symmetricFunctionToBoundedDegree_range_isHomogeneous :
    DirectSum.SetLike.IsHomogeneous (boundedDegreeGrading σ R)
      (symmetricFunctionToBoundedDegree σ R).range := by
  intro n f hf
  obtain ⟨g, rfl⟩ := hf
  let p := symmetricFunctionGrading.mk (homogeneousComponent n (g : MvPowerSeries σ R))
    (isHomogeneous_homogeneousComponent (g : MvPowerSeries σ R) n)
    (IsSymmetric.homogeneousComponent (symmetricFunctionSubalgebra.isSymmetric g) n)
  refine ⟨(p : symmetricFunctionSubalgebra σ R), ?_⟩
  apply Subtype.ext
  exact (coe_decompose_boundedDegreeGrading σ R n
    (symmetricFunctionToBoundedDegree σ R g)).symm

instance SymmetricFunctionGrading.gradedAlgebra :
    GradedAlgebra (symmetricFunctionGrading σ R) :=
  GradedAlgebra.comap (boundedDegreeGrading σ R) (symmetricFunctionToBoundedDegree σ R)
    (symmetricFunctionToBoundedDegree_injective σ R)
    (symmetricFunctionToBoundedDegree_range_isHomogeneous σ R)

/-- Every symmetric function has a unique finite homogeneous decomposition. -/
theorem symmetricFunctionGrading_isInternal :
    DirectSum.IsInternal (symmetricFunctionGrading σ R) :=
  DirectSum.Decomposition.isInternal (symmetricFunctionGrading σ R)

/-- Inclusion into bounded-degree series commutes with homogeneous projections. -/
theorem symmetricFunctionToBoundedDegree_proj (n : ℕ) (f : symmetricFunctionSubalgebra σ R) :
    symmetricFunctionToBoundedDegree σ R
        (GradedAlgebra.proj (symmetricFunctionGrading σ R) n f) =
      GradedAlgebra.proj (boundedDegreeGrading σ R) n
        (symmetricFunctionToBoundedDegree σ R f) := by
  let : GradedAlgebra (fun i => (boundedDegreeGrading σ R i).comap
      (symmetricFunctionToBoundedDegree σ R).toLinearMap) :=
    SymmetricFunctionGrading.gradedAlgebra σ R
  exact GradedAlgebra.map_proj_comap (boundedDegreeGrading σ R)
    (symmetricFunctionToBoundedDegree σ R) n f

/-- Inclusion into bounded-degree series preserves each decomposition component. -/
@[simp]
theorem symmetricFunctionToBoundedDegree_decompose (n : ℕ)
    (f : symmetricFunctionSubalgebra σ R) :
    symmetricFunctionToBoundedDegree σ R
        (DirectSum.decompose (symmetricFunctionGrading σ R) f n) =
      (DirectSum.decompose (boundedDegreeGrading σ R)
        (symmetricFunctionToBoundedDegree σ R f) n : boundedDegreeSubalgebra σ R) :=
  symmetricFunctionToBoundedDegree_proj σ R n f

/-- Grading projections are homogeneous components after inclusion into power series. -/
@[simp]
theorem coe_symmetricFunctionGrading_proj (n : ℕ) (f : symmetricFunctionSubalgebra σ R) :
    (GradedAlgebra.proj (symmetricFunctionGrading σ R) n f : MvPowerSeries σ R) =
      homogeneousComponent n (f : MvPowerSeries σ R) := by
  have h := congrArg (fun g : boundedDegreeSubalgebra σ R => (g : MvPowerSeries σ R))
    (symmetricFunctionToBoundedDegree_proj σ R n f)
  simpa only [coe_symmetricFunctionToBoundedDegree, coe_boundedDegreeGrading_proj] using h

/-- The decomposition recovers the usual homogeneous power-series components. -/
@[simp]
theorem coe_decompose_symmetricFunctionGrading (n : ℕ)
    (f : symmetricFunctionSubalgebra σ R) :
    ((DirectSum.decompose (symmetricFunctionGrading σ R) f n :
      symmetricFunctionSubalgebra σ R) : MvPowerSeries σ R) =
        homogeneousComponent n (f : MvPowerSeries σ R) :=
  coe_symmetricFunctionGrading_proj σ R n f

/-- The coefficient formula for a grading projection. -/
theorem coeff_symmetricFunctionGrading_proj (n : ℕ) (d : σ →₀ ℕ)
    (f : symmetricFunctionSubalgebra σ R) :
    coeff d (GradedAlgebra.proj (symmetricFunctionGrading σ R) n f : MvPowerSeries σ R) =
      if d.degree = n then coeff d (f : MvPowerSeries σ R) else 0 := by
  rw [coe_symmetricFunctionGrading_proj, coeff_homogeneousComponent]

/-- The inclusion of a homogeneous piece into the ambient power-series module. -/
def symmetricFunctionGradingToMvPowerSeries (n : ℕ) :
    symmetricFunctionGrading σ R n →ₗ[R] MvPowerSeries σ R :=
  (symmetricFunctionSubalgebra σ R).val.toLinearMap.comp
    (symmetricFunctionGrading σ R n).subtype

@[simp]
theorem symmetricFunctionGradingToMvPowerSeries_apply (n : ℕ)
    (f : symmetricFunctionGrading σ R n) :
    symmetricFunctionGradingToMvPowerSeries σ R n f =
      ((f : symmetricFunctionSubalgebra σ R) : MvPowerSeries σ R) :=
  rfl

end MvPowerSeries
