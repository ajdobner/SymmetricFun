module

public import SymmetricFun.SymmetricFunction.TransitionMatrices.ElementaryMonomial
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Order.Extension.Linear

/-!
# The elementary symmetric basis

Over a commutative ring and an infinite set of variables, the products
`esymmPartGraded σ R μ` form a basis of the degree-`n` symmetric functions.

The binary-matrix coefficient formula makes the transition from
`esymmPartGraded σ R μ.conjugate` to the monomial basis unitriangular with respect
to dominance. A linear extension is used locally to compute its determinant.
Reindexing by conjugation gives the basis with the original partition labels.
-/

@[expose] public section
noncomputable section

namespace MvPowerSeries

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

end MvPowerSeries
