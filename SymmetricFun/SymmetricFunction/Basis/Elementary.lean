module

public import SymmetricFun.Partition.Multiplicity
public import SymmetricFun.SymmetricFunction.Basis.Transition.ElementaryMonomial
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Order.Extension.Linear
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The elementary symmetric basis and polynomial presentation

Over a commutative ring and an infinite set of variables, the products
`esymmPartGraded σ R μ` form a basis of the degree-`n` symmetric functions.

The binary-matrix coefficient formula makes the transition from
`esymmPartGraded σ R μ.conjugate` to the monomial basis unitriangular with respect
to dominance. A linear extension is used locally to compute its determinant.
Reindexing by conjugation gives the basis with the original partition labels.
The grading then assembles these bases into `esymmPart_basis_all`.

The homomorphism `esymmAlgHom` sends the variable indexed by a positive integer
`i` to the elementary symmetric function `esymm σ R i`. Polynomial monomials
correspond to partitions through multiplicities of positive parts, and evaluation
identifies the polynomial monomial basis with the elementary symmetric basis.
This gives the algebra equivalence `esymmAlgEquiv`, the fundamental theorem of
symmetric functions.

The grading is weighted on the polynomial side, with the variable indexed by
`i` having degree `i`. `esymmAlgEquiv_mem_grading_iff` identifies these weighted
homogeneous pieces with `symmetricFunctionGrading`.
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

section CommSemiring

variable [CommSemiring R]

/-- Evaluate a polynomial in the elementary symmetric functions of positive degree. -/
def esymmAlgHom :
    MvPolynomial ℕ+ R →ₐ[R] symmetricFunctionSubalgebra σ R :=
  MvPolynomial.aeval (fun i : ℕ+ =>
    (esymmGraded σ R (i : ℕ) : symmetricFunctionSubalgebra σ R))

@[simp]
theorem esymmAlgHom_X (i : ℕ+) :
    esymmAlgHom σ R (MvPolynomial.X i) =
      (esymmGraded σ R (i : ℕ) : symmetricFunctionSubalgebra σ R) := by
  simp [esymmAlgHom]

/-- A polynomial monomial evaluates to the elementary product with those part multiplicities. -/
theorem esymmAlgHom_monomial (a : ℕ+ →₀ ℕ) (r : R) :
    esymmAlgHom σ R (MvPolynomial.monomial a r) =
      r • (esymmPartGraded σ R (AllPartitions.ofMultiplicities a).2 :
        symmetricFunctionSubalgebra σ R) := by
  have hprod :
      (((AllPartitions.ofMultiplicities a).parts).map (esymm σ R)).prod =
        a.prod (fun i k => esymm σ R (i : ℕ) ^ k) := by
    rw [AllPartitions.parts_ofMultiplicities, Multiset.map_map, Finsupp.toMultiset_map,
      Finsupp.prod_toMultiset,
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    rfl
  rw [esymmAlgHom, MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  apply congrArg (r • ·)
  apply Subtype.ext
  change (symmetricFunctionSubalgebra σ R).val
      (a.prod (fun i k => (esymmGraded σ R (i : ℕ) :
        symmetricFunctionSubalgebra σ R) ^ k)) =
    esymmPart σ R (AllPartitions.ofMultiplicities a).2
  rw [map_finsuppProd]
  simp only [map_pow]
  exact hprod.symm

/-- Evaluation sends weighted homogeneous polynomials to the corresponding symmetric piece. -/
theorem esymmAlgHom_mem_grading {n : ℕ} {p : MvPolynomial ℕ+ R}
    (hp : p ∈ MvPolynomial.weightedHomogeneousSubmodule R PNat.val n) :
    esymmAlgHom σ R p ∈ symmetricFunctionGrading σ R n := by
  change p.IsWeightedHomogeneous PNat.val n at hp
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
    rw [map_zero]
    exact (symmetricFunctionGrading σ R n).zero_mem
  | add p q hp hq ihp ihq =>
    rw [map_add]
    exact (symmetricFunctionGrading σ R n).add_mem ihp ihq
  | monomial a r ha =>
    rw [esymmAlgHom_monomial]
    apply (symmetricFunctionGrading σ R n).smul_mem
    rw [← ha, ← AllPartitions.size_ofMultiplicities]
    exact (esymmPartGraded σ R (AllPartitions.ofMultiplicities a).2).property

/-- Evaluation commutes with projection onto each weighted homogeneous component. -/
theorem esymmAlgHom_weightedHomogeneousComponent (n : ℕ) (p : MvPolynomial ℕ+ R) :
    esymmAlgHom σ R (MvPolynomial.weightedHomogeneousComponent PNat.val n p) =
      GradedAlgebra.proj (symmetricFunctionGrading σ R) n (esymmAlgHom σ R p) := by
  let : GradedAlgebra (MvPolynomial.weightedHomogeneousSubmodule R PNat.val) :=
    MvPolynomial.weightedGradedAlgebra R PNat.val
  let f : MvPolynomial.weightedHomogeneousSubmodule R PNat.val →ₐᵍ[R]
      symmetricFunctionGrading σ R :=
    { esymmAlgHom σ R with map_mem := esymmAlgHom_mem_grading σ R }
  have h := map_directSumDecompose (MvPolynomial.weightedHomogeneousSubmodule R PNat.val)
    (symmetricFunctionGrading σ R) f (x := p) (i := n)
  change esymmAlgHom σ R (MvPolynomial.decompose' R PNat.val p n : MvPolynomial ℕ+ R) = _ at h
  rw [MvPolynomial.decompose'_apply] at h
  exact h

end CommSemiring

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

/-- Symmetric functions are a polynomial algebra on the elementary symmetric functions
of positive degree. -/
def esymmAlgEquiv :
    MvPolynomial ℕ+ R ≃ₐ[R] symmetricFunctionSubalgebra σ R :=
  AlgEquiv.ofBijective (esymmAlgHom σ R) (esymmAlgHom_bijective σ R)

@[simp]
theorem esymmAlgEquiv_toAlgHom : (esymmAlgEquiv σ R).toAlgHom = esymmAlgHom σ R := rfl

@[simp]
theorem esymmAlgEquiv_apply (p : MvPolynomial ℕ+ R) :
    esymmAlgEquiv σ R p = esymmAlgHom σ R p := rfl

@[simp]
theorem esymmAlgEquiv_X (i : ℕ+) :
    esymmAlgEquiv σ R (MvPolynomial.X i) =
      (esymmGraded σ R (i : ℕ) : symmetricFunctionSubalgebra σ R) :=
  esymmAlgHom_X σ R i

@[simp]
theorem esymmAlgEquiv_symm_esymmGraded (i : ℕ+) :
    (esymmAlgEquiv σ R).symm
        (esymmGraded σ R (i : ℕ) : symmetricFunctionSubalgebra σ R) =
      MvPolynomial.X i := by
  apply (esymmAlgEquiv σ R).injective
  simp

/-- The inverse sends an elementary product to the monomial of its part multiplicities. -/
@[simp]
theorem esymmAlgEquiv_symm_esymmPartGraded {n : ℕ} (μ : Nat.Partition n) :
    (esymmAlgEquiv σ R).symm
        (esymmPartGraded σ R μ : symmetricFunctionSubalgebra σ R) =
      MvPolynomial.monomial μ.toAllPartitions.multiplicities 1 := by
  apply (esymmAlgEquiv σ R).injective
  simp only [AlgEquiv.apply_symm_apply, esymmAlgEquiv_apply, esymmAlgHom_monomial,
    one_smul]
  exact congrArg (fun ν : AllPartitions =>
    (esymmPartGraded σ R ν.2 : symmetricFunctionSubalgebra σ R))
    (AllPartitions.ofMultiplicities_multiplicities μ.toAllPartitions).symm

/-- The algebra equivalence identifies weighted homogeneous polynomials with the
homogeneous pieces of symmetric functions. The variable indexed by `i` has weight `i`. -/
theorem esymmAlgEquiv_mem_grading_iff (n : ℕ) (p : MvPolynomial ℕ+ R) :
    esymmAlgEquiv σ R p ∈ symmetricFunctionGrading σ R n ↔
      p ∈ MvPolynomial.weightedHomogeneousSubmodule R PNat.val n := by
  refine ⟨fun hp => ?_, esymmAlgHom_mem_grading σ R⟩
  have h : MvPolynomial.weightedHomogeneousComponent PNat.val n p = p :=
    (esymmAlgEquiv σ R).injective (by
      change esymmAlgHom σ R (MvPolynomial.weightedHomogeneousComponent PNat.val n p) =
        esymmAlgHom σ R p
      rw [esymmAlgHom_weightedHomogeneousComponent]
      exact DirectSum.decompose_of_mem_same (symmetricFunctionGrading σ R) hp)
  exact h ▸ MvPolynomial.weightedHomogeneousComponent_mem PNat.val p n

@[simp]
theorem isHomogeneous_esymmAlgEquiv_iff (n : ℕ) (p : MvPolynomial ℕ+ R) :
    IsHomogeneous (esymmAlgEquiv σ R p : MvPowerSeries σ R) n ↔
      p.IsWeightedHomogeneous PNat.val n :=
  esymmAlgEquiv_mem_grading_iff σ R n p

end CommRing

end MvPowerSeries
