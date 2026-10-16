import SymmetricFunctions.Hall.Schur
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Faithful tensor Hall coordinates

The tensor Schur basis supplies a coefficient test for bounded tensors. This
does not identify the infinite bounded ring with its full algebraic dual.
-/
noncomputable section
namespace SymmetricFunction
open scoped TensorProduct
variable {R : Type*} [CommRing R]

/-- Tensor Hall pairing with Schur vectors reads the corresponding tensor-basis coordinate. -/
theorem tensorHall_schur (z : SymmetricFunction R ⊗[R] SymmetricFunction R)
    (ξ μ : Σ d, Nat.Partition d) :
    tensorHall z (schur ξ.2 ⊗ₜ[R] schur μ.2) =
      ((schurBasisAll R).tensorProduct (schurBasisAll R)).repr z (ξ, μ) := by
  induction z with
  | tmul f g =>
    rw [tensorHall_tmul, hall_schur_right, hall_schur_right,
      Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, mul_comm]
  | add z w hz hw =>
    simpa only [map_add, LinearMap.add_apply, Finsupp.add_apply] using congrArg₂ (· + ·) hz hw

/-- Equality of all tensor Schur pairings detects equality of bounded tensors. -/
theorem tensorHall_schur_ext {z w : SymmetricFunction R ⊗[R] SymmetricFunction R}
    (h : ∀ (ξ μ : Σ d, Nat.Partition d),
      tensorHall z (schur ξ.2 ⊗ₜ[R] schur μ.2) =
        tensorHall w (schur ξ.2 ⊗ₜ[R] schur μ.2)) : z = w := by
  apply ((schurBasisAll R).tensorProduct (schurBasisAll R)).repr.injective
  ext ⟨ξ, μ⟩
  simpa only [tensorHall_schur] using h ξ μ

end SymmetricFunction
