module

public import SymmetricFun.SymmetricFunction.Basis.Transition.SchurMonomial
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Order.Extension.Linear

/-!
# The Schur basis

Over a commutative ring and an infinite set of variables, the Schur functions form
a basis of each homogeneous piece and of the whole symmetric-function algebra.

Their transition matrix to the monomial basis is the Kostka matrix. It is
unitriangular with respect to any linear extension of dominance, so its determinant
is one. As for the elementary basis, the linear order is used only locally.
-/

@[expose] public section
noncomputable section

namespace MvPowerSeries

variable (σ R : Type*) [CommRing R] [Infinite σ]

/-- The Schur-to-monomial transition matrix has determinant one. -/
theorem det_toMatrix_ssymmPartGraded (n : ℕ) :
    ((msymmPart_basis σ R n).toMatrix (ssymmPartGraded σ R)).det = 1 := by
  classical
  let : PartialOrder (Nat.Partition n) := Nat.Partition.dominanceOrder n
  have hmono := (toLinearExtension (α := Nat.Partition n)).monotone
  let linearOrder : LinearOrder (Nat.Partition n) :=
    inferInstanceAs (LinearOrder (LinearExtension (Nat.Partition n)))
  let : PartialOrder (Nat.Partition n) := linearOrder.toPartialOrder
  have htri : ((msymmPart_basis σ R n).toMatrix (ssymmPartGraded σ R)).IsUpperTriangular := by
    intro μ ν hlt
    change (msymmPart_basis σ R n).repr (ssymmPartGraded σ R ν) μ = 0
    apply msymmPart_basis_repr_ssymmPartGraded_eq_zero σ R
    intro hdom
    exact (not_le_of_gt hlt) (hmono hdom)
  rw [Matrix.det_of_isUpperTriangular htri]
  apply Finset.prod_eq_one
  intro μ _
  change (msymmPart_basis σ R n).repr (ssymmPartGraded σ R μ) μ = 1
  exact msymmPart_basis_repr_ssymmPartGraded_self σ R μ

/-- Schur functions form a basis of each homogeneous piece. -/
def ssymmPart_basis (n : ℕ) :
    Module.Basis (Nat.Partition n) R (symmetricFunctionGrading σ R n) := by
  classical
  have h := ((msymmPart_basis σ R n).is_basis_iff_det
    (v := ssymmPartGraded σ R)).mpr (by
      rw [Module.Basis.det_apply, det_toMatrix_ssymmPartGraded σ R n]
      exact isUnit_one)
  exact Module.Basis.mk h.1 h.2.ge

@[simp]
theorem ssymmPart_basis_apply {n : ℕ} (μ : Nat.Partition n) :
    ssymmPart_basis σ R n μ = ssymmPartGraded σ R μ := by
  simp only [ssymmPart_basis, Module.Basis.mk_apply]

/-- Schur functions form a basis of the whole symmetric-function algebra. -/
def ssymmPart_basis_all :
    Module.Basis IntegerPartition R (symmetricFunctionSubalgebra σ R) :=
  (symmetricFunctionGrading_isInternal σ R).collectedBasis (ssymmPart_basis σ R)

@[simp]
theorem ssymmPart_basis_all_apply (μ : IntegerPartition) :
    ssymmPart_basis_all σ R μ =
      (ssymmPartGraded σ R μ.2 : symmetricFunctionSubalgebra σ R) := by
  simp [ssymmPart_basis_all]

end MvPowerSeries
