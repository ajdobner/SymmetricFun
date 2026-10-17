import SymmetricFunctions.Schur.AlternantPairing
import SymmetricFunctions.Basis.Schur

/-!
# Schur orthonormality for the classical Hall pairing

The pairing is the complete/monomial pairing already constructed. The proof
uses the integral bialternant identity for the actual Jacobi–Trudi determinants.
-/

noncomputable section
namespace SymmetricFunction
open SymmetricFunctions SymmetricFunctions.Partition
variable {R : Type*} [CommRing R]

open Classical in
/-- The actual Schur determinant basis is Hall orthonormal over every commutative ring. -/
@[simp] theorem hall_schur_schur (ξ μ : Σ d, Nat.Partition d) :
    hall (schur (R := R) ξ.2) (schur μ.2) = if ξ = μ then 1 else 0 := by
  let N := max (length ξ.2) (length μ.2)
  have hξ : length ξ.2 ≤ N := le_max_left _ _
  have hμ : length μ.2 ≤ N := le_max_right _ _
  rw [hall_schur_eq_alternating_coeff ξ.2 hξ, mul_comm,
    bialternant_schur μ.2 hμ, coeff_partitionAlternant ξ μ hξ hμ]

/-- Hall pairing with a Schur vector extracts the matching full Schur coefficient. -/
@[simp] theorem hall_schur (ξ : Σ d, Nat.Partition d) (f : SymmetricFunction R) :
    hall (schur ξ.2) f = (schurBasisAll R).repr f ξ := by
  have he : hall (schur (R := R) ξ.2) = (schurBasisAll R).coord ξ := by
    apply (schurBasisAll R).ext
    intro μ
    rw [schurBasisAll_apply, hall_schur_schur]
    change _ = (schurBasisAll R).repr (schur μ.2) ξ
    rw [← schurBasisAll_apply μ, Module.Basis.repr_self, Finsupp.single_apply]
    simp only [eq_comm]
  exact DFunLike.congr_fun he f

/-- Coefficient extraction in the second argument follows from symmetry. -/
@[simp] theorem hall_schur_right (f : SymmetricFunction R) (ξ : Σ d, Nat.Partition d) :
    hall f (schur ξ.2) = (schurBasisAll R).repr f ξ := by
  rw [hall_symm, hall_schur]

/-- In a homogeneous degree, the pairing extracts the finite Schur-basis coordinate. -/
theorem hall_schur_homogeneous {d : ℕ} (ξ : Nat.Partition d)
    (f : homogeneousSubmodule R d) : hall (schur ξ) f = (schurBasis R d).repr f ξ := by
  rw [hall_schur (⟨d, ξ⟩ : Σ d, Nat.Partition d), schurBasisAll_repr]
  have he : decompose R (f : SymmetricFunction R) d = f :=
    Subtype.ext (homogeneousComponent_of_mem f.property)
  rw [he]

open Classical in
/-- The finite Schur basis is orthonormal for the degreewise perfect pairing. -/
@[simp] theorem hallHomogeneous_schurBasis (d : ℕ) (ξ μ : Nat.Partition d) :
    hallHomogeneous R d (schurBasis R d ξ) (schurBasis R d μ) =
      if ξ = μ then 1 else 0 := by
  rw [hallHomogeneous_apply, schurBasis_apply, schurBasis_apply,
    hall_schur_schur (⟨d, ξ⟩ : Σ d, Nat.Partition d) ⟨d, μ⟩]
  simp

end SymmetricFunction
