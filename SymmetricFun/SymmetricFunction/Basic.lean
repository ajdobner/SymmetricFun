module

public import SymmetricFun.MvPowerSeries.BoundedDegree
public import SymmetricFun.MvPowerSeries.Symmetric

/-!
# The algebra of symmetric functions

The concrete algebra consists of bounded-degree power series invariant under all
permutations of the variables. Its inclusion into the bounded-degree algebra
allows the grading to be restricted in `SymmetricFunction/Grading.lean`.
-/

@[expose] public section
noncomputable section

namespace MvPowerSeries

def symmetricFunctionSubalgebra (σ R : Type*) [CommSemiring R] : Subalgebra R (MvPowerSeries σ R) :=
  boundedDegreeSubalgebra σ R ⊓ symmetricSubalgebra σ R

@[simp]
theorem mem_symmetricFunctionSubalgebra [CommSemiring R] (p : MvPowerSeries σ R) :
    p ∈ symmetricFunctionSubalgebra σ R ↔ p.HasBoundedDegree ∧ p.IsSymmetric := by
  change p ∈ boundedDegreeSubalgebra σ R ∧ p ∈ symmetricSubalgebra σ R ↔
    p.HasBoundedDegree ∧ p.IsSymmetric
  simp

theorem mem_symmetricFunctionSubalgebra_of_isHomogeneous {σ R : Type*} [CommSemiring R]
    {n : ℕ} {f : MvPowerSeries σ R} (hf : IsHomogeneous f n) (hs : IsSymmetric f) :
    f ∈ symmetricFunctionSubalgebra σ R :=
  ⟨mem_boundedDegreeSubalgebra_of_isHomogeneous hf, hs⟩

namespace symmetricFunctionSubalgebra

variable {σ R : Type*} [CommSemiring R]

/-- The underlying power series of a symmetric function is symmetric. -/
theorem isSymmetric (f : symmetricFunctionSubalgebra σ R) :
    IsSymmetric (f : MvPowerSeries σ R) :=
  f.property.2

/-- The underlying power series of a symmetric function has bounded degree. -/
theorem hasBoundedDegree (f : symmetricFunctionSubalgebra σ R) :
    HasBoundedDegree (f : MvPowerSeries σ R) :=
  mem_boundedDegreeSubalgebra.mp f.property.1

end symmetricFunctionSubalgebra

/-- The inclusion of symmetric functions into bounded-degree power series. -/
def symmetricFunctionToBoundedDegree (σ R : Type*) [CommSemiring R] :
    symmetricFunctionSubalgebra σ R →ₐ[R] boundedDegreeSubalgebra σ R :=
  Subalgebra.inclusion inf_le_left

@[simp]
theorem coe_symmetricFunctionToBoundedDegree {σ R : Type*} [CommSemiring R]
    (f : symmetricFunctionSubalgebra σ R) :
    (symmetricFunctionToBoundedDegree σ R f : MvPowerSeries σ R) = f :=
  rfl

theorem symmetricFunctionToBoundedDegree_injective (σ R : Type*) [CommSemiring R] :
    Function.Injective (symmetricFunctionToBoundedDegree σ R) := by
  intro f g h
  exact Subtype.ext (congrArg
    (fun b : boundedDegreeSubalgebra σ R => (b : MvPowerSeries σ R)) h)

end MvPowerSeries
