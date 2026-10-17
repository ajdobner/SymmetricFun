import SymmetricFunctions.Schur.Tableaux
import SymmetricFunctions.Tableaux.Kostka

/-!
# Kostka coefficients of the existing Schur functions

The natural number counts tableaux of one fixed decreasing content. The monomial
symmetric function has coefficient one at each exponent in its orbit, so no
permutation or repeated-part factorial occurs. All coefficient identities hold
over arbitrary commutative rings; equality of natural counts is proved over ℤ.
-/
noncomputable section
open scoped BigOperators

namespace SymmetricFunction
open SymmetricFunctions SymmetricFunctions.Partition
variable {R : Type*} [CommRing R] {d N : ℕ}

/-- Monomial coordinates of Schur functions are the natural tableau counts. -/
theorem mBasis_repr_schur (ξ μ : Nat.Partition d) :
    (mBasis R d).repr ⟨schur ξ, isHomogeneous_schur ξ⟩ μ = (kostka ξ μ : R) := by
  rw [mBasis_repr_eq_coeff _ μ d (rowContent μ d)
    (exponentParts_rowContent μ (parts_card_le μ)),
    ← alphabetSpecialization_fin, coeff_alphabetSpecialization_schur]
  rfl

/-- Every sufficiently padded decreasing content counts the same tableaux. -/
theorem contentCount_rowContent (ξ μ : Nat.Partition d) (hN : length μ ≤ N) :
    FiniteTableau.contentCount ξ (rowContent μ N) = kostka ξ μ := by
  apply Nat.cast_injective (R := ℤ)
  rw [← coeff_alphabetSpecialization_schur, alphabetSpecialization_fin,
    ← mBasis_repr_eq_coeff ⟨schur ξ, isHomogeneous_schur ξ⟩ μ N
      (rowContent μ N) (exponentParts_rowContent μ hN), mBasis_repr_schur]

/-- A coefficient of any exponent with partition shape μ is the same Kostka number. -/
theorem coeff_schur_eq_kostka (ξ μ : Nat.Partition d) (a : Fin N →₀ ℕ)
    (ha : exponentParts a = μ.parts) :
    (alphabetSpecialization R (Fin N) (schur ξ)).coeff a = (kostka ξ μ : R) := by
  rw [alphabetSpecialization_fin,
    ← mBasis_repr_eq_coeff ⟨schur ξ, isHomogeneous_schur ξ⟩ μ N a ha,
    mBasis_repr_schur]

/-- Natural counts depend only on content shape, in every alphabet where it occurs. -/
theorem contentCount_eq_kostka (ξ μ : Nat.Partition d) (a : Fin N →₀ ℕ)
    (ha : exponentParts a = μ.parts) : FiniteTableau.contentCount ξ a = kostka ξ μ := by
  apply Nat.cast_injective (R := ℤ)
  rw [← coeff_alphabetSpecialization_schur, coeff_schur_eq_kostka ξ μ a ha]

/-- The classical integral monomial expansion, valid also in torsion and the zero ring. -/
theorem schur_eq_sum_kostka_mPart (ξ : Nat.Partition d) :
    schur (R := R) ξ = ∑ μ : Nat.Partition d, (kostka ξ μ : R) • mPart μ := by
  have he := congrArg (fun f : homogeneousSubmodule R d => (f : SymmetricFunction R))
    ((mBasis R d).sum_repr ⟨schur ξ, isHomogeneous_schur ξ⟩)
  simpa only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul,
    mBasis_apply, mBasis_repr_schur] using he.symm

/-- Nonnegativity refers to integers, not an order on arbitrary coefficient rings. -/
theorem mBasis_repr_schur_nonneg (ξ μ : Nat.Partition d) :
    0 ≤ (mBasis ℤ d).repr ⟨schur ξ, isHomogeneous_schur ξ⟩ μ := by
  rw [mBasis_repr_schur]
  exact Nat.cast_nonneg _

end SymmetricFunction
