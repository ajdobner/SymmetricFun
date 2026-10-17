import SymmetricFunctions.Basis.Complete
import SymmetricFunctions.Basis.Monomial
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# The classical Hall pairing

Complete and monomial partition vectors are dual. The defining expansion is
finite because symmetric functions have bounded degree. Perfectness is stated
only on a single homogeneous component.
-/

noncomputable section

namespace SymmetricFunction

open SymmetricFunctions
open scoped TensorProduct
variable {R : Type*} [CommRing R]

/-- The Hall pairing, normalized by complete/monomial duality. -/
def hall : SymmetricFunction R →ₗ[R] SymmetricFunction R →ₗ[R] R :=
  (hBasisAll R).constr R (fun μ => (mBasisAll R).coord μ)

/-- Pairing a complete vector reads the corresponding monomial coordinate. -/
@[simp] theorem hall_hPart (μ : Σ d, Nat.Partition d) (f : SymmetricFunction R) :
    hall (hPart μ.2) f = (mBasisAll R).repr f μ := by
  rw [← hBasisAll_apply μ]
  exact LinearMap.congr_fun ((hBasisAll R).constr_basis R _ μ) f

/-- The normalization includes distinct degrees and the empty partition. -/
@[simp] theorem hall_hPart_mPart (μ ν : Σ d, Nat.Partition d) :
    hall (hPart (R := R) μ.2) (mPart ν.2) = if μ = ν then 1 else 0 := by
  rw [hall_hPart, ← mBasisAll_apply ν]
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  simp only [eq_comm]

/-- Pairing against a monomial vector reads a complete coordinate. -/
@[simp] theorem hall_mPart (f : SymmetricFunction R) (ν : Σ d, Nat.Partition d) :
    hall f (mPart ν.2) = (hBasisAll R).repr f ν := by
  have he : hall.flip (mPart (R := R) ν.2) = (hBasisAll R).coord ν := by
    apply (hBasisAll R).ext
    intro μ
    rw [hBasisAll_apply, LinearMap.flip_apply, hall_hPart_mPart]
    change _ = (hBasisAll R).repr (hPart μ.2) ν
    rw [← hBasisAll_apply μ, Module.Basis.repr_self, Finsupp.single_apply]
  exact DFunLike.congr_fun he f

/-- Nondegeneracy in the first variable does not require a field. -/
theorem hall_left_nondegenerate {f : SymmetricFunction R}
    (hf : ∀ g, hall f g = 0) : f = 0 := by
  apply (hBasisAll R).repr.injective
  ext μ
  simpa only [map_zero, Finsupp.zero_apply, hall_mPart] using hf (mPart μ.2)

/-- Nondegeneracy in the second variable does not require a field. -/
theorem hall_right_nondegenerate {g : SymmetricFunction R}
    (hg : ∀ f, hall f g = 0) : g = 0 := by
  apply (mBasisAll R).repr.injective
  ext μ
  simpa only [map_zero, Finsupp.zero_apply, hall_hPart] using hg (hPart μ.2)

/-- Complete and monomial coordinates in a fixed degree agree with the full basis. -/
theorem hall_hPart_homogeneous {d : ℕ} (μ : Nat.Partition d)
    (f : homogeneousSubmodule R d) :
    hall (hPart μ) f = (mBasis R d).repr f μ := by
  rw [hall_hPart (⟨d, μ⟩ : Σ d, Nat.Partition d), mBasisAll_repr,
    homogeneousComponent_of_mem f.property, mBasis_repr]

/-- Distinct weighted degrees are orthogonal. -/
theorem hall_eq_zero_of_degrees_ne {d e : ℕ} {f g : SymmetricFunction R}
    (hf : IsHomogeneous f d) (hg : IsHomogeneous g e) (hde : d ≠ e) : hall f g = 0 := by
  have hh (μ : Nat.Partition d) : hall (hPart (R := R) μ) g = 0 := by
    rw [hall_hPart (⟨d, μ⟩ : Σ d, Nat.Partition d), mBasisAll_repr,
      homogeneousComponent_of_mem_ne hg hde.symm]
    simp
  have he := congrArg (fun x : homogeneousSubmodule R d => hall (x : SymmetricFunction R) g)
    ((hBasis R d).sum_repr ⟨f, hf⟩)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, map_sum, LinearMap.sum_apply,
    map_smul, LinearMap.smul_apply, hBasis_apply, hh, smul_zero,
    Finset.sum_const_zero] using he.symm

/-- Restriction of the pairing to one homogeneous component. -/
def hallHomogeneous (R : Type*) [CommRing R] (d : ℕ) :
    homogeneousSubmodule R d →ₗ[R] homogeneousSubmodule R d →ₗ[R] R :=
  hall.compl₁₂ (homogeneousSubmodule R d).subtype (homogeneousSubmodule R d).subtype

@[simp] theorem hallHomogeneous_apply (d : ℕ) (f g : homogeneousSubmodule R d) :
    hallHomogeneous R d f g = hall (f : SymmetricFunction R) g := rfl

/-- Degreewise perfectness, matching the complete basis with the dual monomial basis. -/
def hallHomogeneousPerfect (R : Type*) [CommRing R] (d : ℕ) :
    homogeneousSubmodule R d ≃ₗ[R] Module.Dual R (homogeneousSubmodule R d) :=
  (hBasis R d).equiv (mBasis R d).dualBasis (Equiv.refl _)

@[simp] theorem hallHomogeneousPerfect_apply (d : ℕ) (f g : homogeneousSubmodule R d) :
    hallHomogeneousPerfect R d f g = hall (f : SymmetricFunction R) g := by
  have he : (hallHomogeneousPerfect R d).toLinearMap = hallHomogeneous R d := by
    apply (hBasis R d).ext
    intro μ
    ext g
    simp [hallHomogeneousPerfect, Module.Basis.equiv_apply,
      hall_hPart_homogeneous]
  exact LinearMap.congr_fun (LinearMap.congr_fun he f) g

/-- Both arguments induce equivalences with the dual in each degree. -/
instance hallHomogeneous_isPerfPair (R : Type*) [CommRing R] (d : ℕ) :
    (hallHomogeneous R d).IsPerfPair := by
  constructor
  · have he : hallHomogeneous R d = (hallHomogeneousPerfect R d).toLinearMap := by
      ext f g
      simp
    rw [he]
    exact (hallHomogeneousPerfect R d).bijective
  · let e := (mBasis R d).equiv (hBasis R d).dualBasis (Equiv.refl _)
    have he : (hallHomogeneous R d).flip = e.toLinearMap := by
      apply (mBasis R d).ext
      intro μ
      apply (hBasis R d).ext
      intro ν
      simp only [LinearMap.flip_apply, hallHomogeneous_apply, hBasis_apply, mBasis_apply]
      rw [hall_hPart_mPart (⟨d, ν⟩ : Σ d, Nat.Partition d) ⟨d, μ⟩]
      simp [e, Module.Basis.equiv_apply, Finsupp.single_apply, eq_comm]
    rw [he]
    exact e.bijective

/-- Product pairing on the ordinary tensor product of bounded symmetric functions. -/
def tensorHall : (SymmetricFunction R ⊗[R] SymmetricFunction R) →ₗ[R]
    (SymmetricFunction R ⊗[R] SymmetricFunction R) →ₗ[R] R :=
  LinearMap.BilinForm.tensorDistrib R R (hall ⊗ₜ[R] hall)

@[simp] theorem tensorHall_tmul (f g u v : SymmetricFunction R) :
    tensorHall (f ⊗ₜ[R] g) (u ⊗ₜ[R] v) = hall f u * hall g v := by
  simp [tensorHall, mul_comm]

end SymmetricFunction
