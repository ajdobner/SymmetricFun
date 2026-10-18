module

public import SymmetricFun.SymmetricFunction.Omega

/-!
# The complete homogeneous basis and polynomial presentation

Over a commutative ring and an infinite variable type, the complete homogeneous
products form a basis in each degree and in the whole symmetric-function algebra.
The bases `hsymmPart_basis` and `hsymmPart_basis_all` are obtained by transporting
the elementary bases through `omega`.

Composing the elementary polynomial presentation with `omega` proves that complete
homogeneous evaluation is bijective. `hsymmGradedAlgEquiv` promotes the evaluation map
from `Basis/Defs.lean` to an equivalence, so its forward map is definitionally
`hsymmAlgHom`. The variable indexed by a positive integer `i` has weight `i`;
`hsymmAlgEquiv` is the underlying algebra equivalence.
-/

@[expose] public section
noncomputable section

namespace MvPowerSeries

variable (σ R : Type*) [CommRing R] [Infinite σ]

/-! ## Complete homogeneous basis -/

/-- The complete homogeneous products form a basis of each homogeneous piece. -/
def hsymmPart_basis (n : ℕ) :
    Module.Basis (Nat.Partition n) R (symmetricFunctionGrading σ R n) :=
  (esymmPart_basis σ R n).map ((omega σ R).gradedLinearEquiv n)

@[simp]
theorem hsymmPart_basis_apply {n : ℕ} (μ : Nat.Partition n) :
    hsymmPart_basis σ R n μ = hsymmPartGraded σ R μ := by
  simp only [hsymmPart_basis, Module.Basis.map_apply, esymmPart_basis_apply]
  apply Subtype.ext
  exact omega_esymmPartGraded σ R μ

/-- The complete homogeneous products form a basis of the whole symmetric-function algebra. -/
def hsymmPart_basis_all :
    Module.Basis IntegerPartition R (symmetricFunctionSubalgebra σ R) :=
  (esymmPart_basis_all σ R).map (omega σ R).toAlgEquiv.toLinearEquiv

@[simp]
theorem hsymmPart_basis_all_apply (μ : IntegerPartition) :
    hsymmPart_basis_all σ R μ =
      (hsymmPartGraded σ R μ.2 : symmetricFunctionSubalgebra σ R) := by
  change omega σ R (esymmPart_basis_all σ R μ) = _
  rw [esymmPart_basis_all_apply, omega_esymmPartGraded]

/-! ## Polynomial presentation -/

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- Evaluation in the complete homogeneous symmetric functions is bijective. -/
theorem hsymmAlgHom_bijective : Function.Bijective (hsymmAlgHom σ R) := by
  have h : ⇑((esymmGradedAlgEquiv σ R).trans (omega σ R)) = hsymmAlgHom σ R := by
    funext p
    change hsymmAlgHom σ R ((esymmGradedAlgEquiv σ R).symm
      (esymmGradedAlgEquiv σ R p)) = hsymmAlgHom σ R p
    rw [GradedAlgEquiv.symm_apply_apply]
  rw [← h]
  exact ((esymmGradedAlgEquiv σ R).trans (omega σ R)).bijective

/-- Symmetric functions are a graded polynomial algebra on the complete homogeneous
functions of positive degree, with the variable indexed by `i` having weight `i`. -/
def hsymmGradedAlgEquiv :
    MvPolynomial.weightedHomogeneousSubmodule R PNat.val ≃ₐᵍ[R]
      symmetricFunctionGrading σ R :=
  GradedAlgEquiv.ofBijective (hsymmGradedAlgHom σ R) (hsymmAlgHom_bijective σ R)

@[simp]
theorem hsymmGradedAlgEquiv_toGradedAlgHom :
    (hsymmGradedAlgEquiv σ R).toGradedAlgHom = hsymmGradedAlgHom σ R := rfl

theorem hsymmGradedAlgEquiv_apply (p : MvPolynomial ℕ+ R) :
    hsymmGradedAlgEquiv σ R p = hsymmAlgHom σ R p := rfl

/-- The complete homogeneous presentation is the elementary presentation followed by omega. -/
theorem hsymmGradedAlgEquiv_eq_esymmGradedAlgEquiv_trans_omega :
    hsymmGradedAlgEquiv σ R = (esymmGradedAlgEquiv σ R).trans (omega σ R) := by
  apply GradedAlgEquiv.ext
  intro p
  change hsymmAlgHom σ R p = hsymmAlgHom σ R ((esymmGradedAlgEquiv σ R).symm
    (esymmGradedAlgEquiv σ R p))
  rw [GradedAlgEquiv.symm_apply_apply]

/-- The inverse applies omega before taking elementary polynomial coordinates. -/
theorem hsymmGradedAlgEquiv_symm_apply (f : symmetricFunctionSubalgebra σ R) :
    (hsymmGradedAlgEquiv σ R).symm f =
      (esymmGradedAlgEquiv σ R).symm (omega σ R f) := by
  rw [hsymmGradedAlgEquiv_eq_esymmGradedAlgEquiv_trans_omega,
    GradedAlgEquiv.trans_symm, omega_symm, GradedAlgEquiv.trans_apply]

@[simp]
theorem hsymmGradedAlgEquiv_X (i : ℕ+) :
    hsymmGradedAlgEquiv σ R (MvPolynomial.X i) =
      (hsymmGraded σ R (i : ℕ) : symmetricFunctionSubalgebra σ R) :=
  hsymmAlgHom_X σ R i

@[simp]
theorem hsymmGradedAlgEquiv_symm_hsymmGraded (i : ℕ+) :
    (hsymmGradedAlgEquiv σ R).symm
        (hsymmGraded σ R (i : ℕ) : symmetricFunctionSubalgebra σ R) =
      MvPolynomial.X i := by
  apply (hsymmGradedAlgEquiv σ R).injective
  simp

/-- The inverse sends a complete homogeneous product to the monomial of its part multiplicities. -/
@[simp]
theorem hsymmGradedAlgEquiv_symm_hsymmPartGraded {n : ℕ} (μ : Nat.Partition n) :
    (hsymmGradedAlgEquiv σ R).symm
        (hsymmPartGraded σ R μ : symmetricFunctionSubalgebra σ R) =
      MvPolynomial.monomial μ.toIntegerPartition.multiplicities 1 := by
  rw [hsymmGradedAlgEquiv_symm_apply, omega_hsymmPartGraded,
    esymmGradedAlgEquiv_symm_esymmPartGraded]

/-- The underlying algebra equivalence of `hsymmGradedAlgEquiv`. -/
def hsymmAlgEquiv :
    MvPolynomial ℕ+ R ≃ₐ[R] symmetricFunctionSubalgebra σ R :=
  (hsymmGradedAlgEquiv σ R).toAlgEquiv

@[simp]
theorem hsymmGradedAlgEquiv_toAlgEquiv :
    (hsymmGradedAlgEquiv σ R).toAlgEquiv = hsymmAlgEquiv σ R := rfl

@[simp]
theorem hsymmAlgEquiv_toAlgHom : (hsymmAlgEquiv σ R).toAlgHom = hsymmAlgHom σ R := rfl

theorem hsymmAlgEquiv_apply (p : MvPolynomial ℕ+ R) :
    hsymmAlgEquiv σ R p = hsymmAlgHom σ R p := rfl

@[simp]
theorem hsymmAlgEquiv_X (i : ℕ+) :
    hsymmAlgEquiv σ R (MvPolynomial.X i) =
      (hsymmGraded σ R (i : ℕ) : symmetricFunctionSubalgebra σ R) :=
  hsymmGradedAlgEquiv_X σ R i

@[simp]
theorem hsymmAlgEquiv_symm_hsymmGraded (i : ℕ+) :
    (hsymmAlgEquiv σ R).symm
        (hsymmGraded σ R (i : ℕ) : symmetricFunctionSubalgebra σ R) =
      MvPolynomial.X i :=
  hsymmGradedAlgEquiv_symm_hsymmGraded σ R i

/-- The inverse sends a complete homogeneous product to the monomial of its part multiplicities. -/
@[simp]
theorem hsymmAlgEquiv_symm_hsymmPartGraded {n : ℕ} (μ : Nat.Partition n) :
    (hsymmAlgEquiv σ R).symm
        (hsymmPartGraded σ R μ : symmetricFunctionSubalgebra σ R) =
      MvPolynomial.monomial μ.toIntegerPartition.multiplicities 1 :=
  hsymmGradedAlgEquiv_symm_hsymmPartGraded σ R μ

/-- The complete homogeneous presentation identifies the weighted homogeneous pieces. -/
theorem hsymmAlgEquiv_mem_grading_iff (n : ℕ) (p : MvPolynomial ℕ+ R) :
    hsymmAlgEquiv σ R p ∈ symmetricFunctionGrading σ R n ↔
      p ∈ MvPolynomial.weightedHomogeneousSubmodule R PNat.val n :=
  (hsymmGradedAlgEquiv σ R).map_mem_iff

@[simp]
theorem isHomogeneous_hsymmAlgEquiv_iff (n : ℕ) (p : MvPolynomial ℕ+ R) :
    IsHomogeneous (hsymmAlgEquiv σ R p : MvPowerSeries σ R) n ↔
      p.IsWeightedHomogeneous PNat.val n :=
  hsymmAlgEquiv_mem_grading_iff σ R n p

end MvPowerSeries
