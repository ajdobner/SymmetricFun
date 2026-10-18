module

public import SymmetricFun.GradedAlgebra.AlgEquiv
public import SymmetricFun.SymmetricFunction.Basis.Transition.ElementaryMonomial
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Order.Extension.Linear

/-!
# The elementary symmetric basis and polynomial presentation

Over a commutative ring and an infinite set of variables, the products
`esymmPartGraded σ R μ` form a basis of the degree-`n` symmetric functions.

The binary-matrix coefficient formula makes the transition from
`esymmPartGraded σ R μ.conjugate` to the monomial basis unitriangular with respect
to dominance. A linear extension is used locally to compute its determinant.
Reindexing by conjugation gives the basis with the original partition labels.
The grading then assembles these bases into `esymmPart_basis_all`.

The homomorphism `esymmAlgHom`, defined in `Basis/Defs.lean`, sends the variable
indexed by a positive integer `i` to the elementary symmetric function `esymm σ R i`.
Polynomial monomials correspond to partitions through multiplicities of positive parts,
and evaluation identifies the polynomial monomial basis with the elementary symmetric basis.
This gives the graded algebra equivalence `esymmGradedAlgEquiv`, the fundamental
theorem of symmetric functions. Its underlying algebra equivalence is `esymmAlgEquiv`.

The grading is weighted on the polynomial side, with the variable indexed by
`i` having degree `i`. `esymmGradedAlgEquiv` identifies these weighted homogeneous
pieces with `symmetricFunctionGrading`; its `gradedLinearEquiv` restricts the
equivalence to any one degree.
-/

@[expose] public section
noncomputable section

namespace MvPowerSeries

/-! ## Elementary symmetric basis -/

section ElementaryBasis

variable (σ R : Type*) [CommRing R] [Infinite σ]

/-- Indexing elementary products by conjugate partitions gives a transition matrix
with determinant one in the monomial basis. -/
theorem det_toMatrix_esymmPartGraded_conjugate (n : ℕ) :
    ((msymmPart_basis σ R n).toMatrix
      (fun μ : Nat.Partition n => esymmPartGraded σ R μ.conjugate)).det = 1 := by
  classical
  -- Extend dominance only for the determinant calculation.
  let : PartialOrder (Nat.Partition n) := Nat.Partition.dominanceOrder n
  have hmono := (toLinearExtension (α := Nat.Partition n)).monotone
  let linearOrder : LinearOrder (Nat.Partition n) :=
    inferInstanceAs (LinearOrder (LinearExtension (Nat.Partition n)))
  let : PartialOrder (Nat.Partition n) := linearOrder.toPartialOrder
  have htri : ((msymmPart_basis σ R n).toMatrix
      (fun μ : Nat.Partition n => esymmPartGraded σ R μ.conjugate)).IsUpperTriangular := by
    intro μ ν hlt
    change (msymmPart_basis σ R n).repr (esymmPartGraded σ R ν.conjugate) μ = 0
    apply msymmPart_basis_repr_esymmPartGraded_eq_zero R
    intro hdom
    have hdom' : ν.Dominates μ := by
      simpa only [Nat.Partition.conjugate_conjugate] using hdom
    exact (not_le_of_gt hlt) (hmono hdom')
  rw [Matrix.det_of_isUpperTriangular htri]
  apply Finset.prod_eq_one
  intro μ _
  change (msymmPart_basis σ R n).repr (esymmPartGraded σ R μ.conjugate) μ = 1
  simpa only [Nat.Partition.conjugate_conjugate] using
    msymmPart_basis_repr_esymmPartGraded_conjugate (σ := σ) R μ.conjugate

/-- The elementary symmetric products form a basis of each homogeneous piece. -/
def esymmPart_basis (n : ℕ) :
    Module.Basis (Nat.Partition n) R (symmetricFunctionGrading σ R n) := by
  classical
  have h := ((msymmPart_basis σ R n).is_basis_iff_det
    (v := fun μ : Nat.Partition n => esymmPartGraded σ R μ.conjugate)).mpr (by
      rw [Module.Basis.det_apply, det_toMatrix_esymmPartGraded_conjugate σ R n]
      exact isUnit_one)
  exact (Module.Basis.mk h.1 h.2.ge).reindex (Nat.Partition.conjugateEquiv n)

@[simp]
theorem esymmPart_basis_apply {n : ℕ} (μ : Nat.Partition n) :
    esymmPart_basis σ R n μ = esymmPartGraded σ R μ := by
  simp only [esymmPart_basis, Module.Basis.reindex_apply, Module.Basis.mk_apply,
    Nat.Partition.conjugateEquiv_symm_apply, Nat.Partition.conjugate_conjugate]

/-- The elementary symmetric products form a basis of the whole symmetric-function algebra. -/
def esymmPart_basis_all :
    Module.Basis AllPartitions R (symmetricFunctionSubalgebra σ R) :=
  (symmetricFunctionGrading_isInternal σ R).collectedBasis (esymmPart_basis σ R)

@[simp]
theorem esymmPart_basis_all_apply (μ : AllPartitions) :
    esymmPart_basis_all σ R μ =
      (esymmPartGraded σ R μ.2 : symmetricFunctionSubalgebra σ R) := by
  simp [esymmPart_basis_all]

end ElementaryBasis

/-! ## Polynomial presentation -/

variable (σ R : Type*)

attribute [local instance] MvPolynomial.weightedGradedAlgebra

section CommRing

variable [CommRing R] [Infinite σ]

/-- Evaluation in the elementary symmetric functions is bijective. -/
theorem esymmAlgHom_bijective : Function.Bijective (esymmAlgHom σ R) := by
  let e := (MvPolynomial.basisMonomials ℕ+ R).equiv
    (esymmPart_basis_all σ R) AllPartitions.multiplicitiesEquiv.symm
  have h : (esymmAlgHom σ R).toLinearMap = e.toLinearMap := by
    apply (MvPolynomial.basisMonomials ℕ+ R).ext
    intro a
    change esymmAlgHom σ R (MvPolynomial.monomial a 1) =
      (MvPolynomial.basisMonomials ℕ+ R).equiv (esymmPart_basis_all σ R)
        AllPartitions.multiplicitiesEquiv.symm ((MvPolynomial.basisMonomials ℕ+ R) a)
    rw [Module.Basis.equiv_apply]
    simp only [esymmPart_basis_all_apply, AllPartitions.multiplicitiesEquiv_symm_apply,
      esymmAlgHom_monomial, one_smul]
  change Function.Bijective (esymmAlgHom σ R).toLinearMap
  rw [h]
  exact e.bijective

/-- Symmetric functions are a graded polynomial algebra on the elementary symmetric
functions of positive degree, with the variable indexed by `i` having weight `i`. -/
def esymmGradedAlgEquiv :
    MvPolynomial.weightedHomogeneousSubmodule R PNat.val ≃ₐᵍ[R]
      symmetricFunctionGrading σ R :=
  GradedAlgEquiv.ofBijective (esymmGradedAlgHom σ R) (esymmAlgHom_bijective σ R)

@[simp]
theorem esymmGradedAlgEquiv_toGradedAlgHom :
    (esymmGradedAlgEquiv σ R).toGradedAlgHom = esymmGradedAlgHom σ R := rfl

theorem esymmGradedAlgEquiv_apply (p : MvPolynomial ℕ+ R) :
    esymmGradedAlgEquiv σ R p = esymmAlgHom σ R p := rfl

@[simp]
theorem esymmGradedAlgEquiv_X (i : ℕ+) :
    esymmGradedAlgEquiv σ R (MvPolynomial.X i) =
      (esymmGraded σ R (i : ℕ) : symmetricFunctionSubalgebra σ R) :=
  esymmAlgHom_X σ R i

@[simp]
theorem esymmGradedAlgEquiv_symm_esymmGraded (i : ℕ+) :
    (esymmGradedAlgEquiv σ R).symm
        (esymmGraded σ R (i : ℕ) : symmetricFunctionSubalgebra σ R) =
      MvPolynomial.X i := by
  apply (esymmGradedAlgEquiv σ R).injective
  simp

/-- The inverse sends an elementary product to the monomial of its part multiplicities. -/
@[simp]
theorem esymmGradedAlgEquiv_symm_esymmPartGraded {n : ℕ} (μ : Nat.Partition n) :
    (esymmGradedAlgEquiv σ R).symm
        (esymmPartGraded σ R μ : symmetricFunctionSubalgebra σ R) =
      MvPolynomial.monomial μ.toAllPartitions.multiplicities 1 := by
  apply (esymmGradedAlgEquiv σ R).injective
  simp only [GradedAlgEquiv.apply_symm_apply, esymmGradedAlgEquiv_apply,
    esymmAlgHom_monomial, one_smul]
  exact congrArg (fun ν : AllPartitions =>
    (esymmPartGraded σ R ν.2 : symmetricFunctionSubalgebra σ R))
    (AllPartitions.ofMultiplicities_multiplicities μ.toAllPartitions).symm

/-- The underlying algebra equivalence of `esymmGradedAlgEquiv`. -/
def esymmAlgEquiv :
    MvPolynomial ℕ+ R ≃ₐ[R] symmetricFunctionSubalgebra σ R :=
  (esymmGradedAlgEquiv σ R).toAlgEquiv

@[simp]
theorem esymmGradedAlgEquiv_toAlgEquiv :
    (esymmGradedAlgEquiv σ R).toAlgEquiv = esymmAlgEquiv σ R := rfl

@[simp]
theorem esymmAlgEquiv_toAlgHom : (esymmAlgEquiv σ R).toAlgHom = esymmAlgHom σ R := rfl

@[simp]
theorem esymmAlgEquiv_apply (p : MvPolynomial ℕ+ R) :
    esymmAlgEquiv σ R p = esymmAlgHom σ R p := rfl

@[simp]
theorem esymmAlgEquiv_X (i : ℕ+) :
    esymmAlgEquiv σ R (MvPolynomial.X i) =
      (esymmGraded σ R (i : ℕ) : symmetricFunctionSubalgebra σ R) :=
  esymmGradedAlgEquiv_X σ R i

@[simp]
theorem esymmAlgEquiv_symm_esymmGraded (i : ℕ+) :
    (esymmAlgEquiv σ R).symm
        (esymmGraded σ R (i : ℕ) : symmetricFunctionSubalgebra σ R) =
      MvPolynomial.X i :=
  esymmGradedAlgEquiv_symm_esymmGraded σ R i

/-- The inverse sends an elementary product to the monomial of its part multiplicities. -/
@[simp]
theorem esymmAlgEquiv_symm_esymmPartGraded {n : ℕ} (μ : Nat.Partition n) :
    (esymmAlgEquiv σ R).symm
        (esymmPartGraded σ R μ : symmetricFunctionSubalgebra σ R) =
      MvPolynomial.monomial μ.toAllPartitions.multiplicities 1 :=
  esymmGradedAlgEquiv_symm_esymmPartGraded σ R μ

/-- The algebra equivalence identifies weighted homogeneous polynomials with the
homogeneous pieces of symmetric functions. The variable indexed by `i` has weight `i`. -/
theorem esymmAlgEquiv_mem_grading_iff (n : ℕ) (p : MvPolynomial ℕ+ R) :
    esymmAlgEquiv σ R p ∈ symmetricFunctionGrading σ R n ↔
      p ∈ MvPolynomial.weightedHomogeneousSubmodule R PNat.val n :=
  (esymmGradedAlgEquiv σ R).map_mem_iff

@[simp]
theorem isHomogeneous_esymmAlgEquiv_iff (n : ℕ) (p : MvPolynomial ℕ+ R) :
    IsHomogeneous (esymmAlgEquiv σ R p : MvPowerSeries σ R) n ↔
      p.IsWeightedHomogeneous PNat.val n :=
  esymmAlgEquiv_mem_grading_iff σ R n p

end CommRing

end MvPowerSeries
