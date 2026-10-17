module

public import Mathlib.LinearAlgebra.Basis.Defs
public import SymmetricFun.Finsupp.Partition
public import SymmetricFun.SymmetricFunction.Grading

/-!
# Monomial symmetric functions and their coordinates

`msymm` takes a partition of `n`, with the degree inferred from the partition.
Its coefficientwise definition is independent of any choice of exponent
representatives. For an index `μ : AllPartitions`, use `msymm σ R μ.2`.
Chosen representatives let `msymmEquivFun` read the coordinates of
a homogeneous symmetric series; `msymmEquivFun_apply_eq_coeff` allows any exponent
vector with the required partition to be used instead.

`msymm_basis` is a basis of the internal degree-`n` piece of the symmetric-function
algebra. Its vectors are `msymmGraded`, and its coordinates are described by
`msymm_basis_repr_apply`.
-/

@[expose] public section
noncomputable section

namespace MvPowerSeries

lemma coeff_eq_of_toAllPartitions_eq {σ R : Type*} [CommSemiring R]
    (m₁ m₂ : σ →₀ ℕ) (f : MvPowerSeries σ R) (hf : f.IsSymmetric)
    (h : m₁.toAllPartitions = m₂.toAllPartitions) :
    coeff m₁ f = coeff m₂ f := by
  obtain ⟨e, rfl⟩ := Finsupp.exists_equivMapDomain_of_toAllPartitions_eq m₁ m₂ h
  exact coeff_equivMapDomain_of_isSymmetric e m₂ f hf

theorem coeff_of_isSymmetric {σ R : Type*} [CommSemiring R] [Infinite σ]
  (m : σ →₀ ℕ) (f : MvPowerSeries σ R) (hf : f.IsSymmetric) :
    coeff m f = coeff (monomialRepresentative σ m.toAllPartitions) f := by
  rw [← coeff_eq_of_toAllPartitions_eq m (monomialRepresentative σ m.toAllPartitions) f hf]
  rw [monomialRepresentative_toAllPartitions]

/-- Homogeneous symmetric series are determined by one coefficient per partition of their degree. -/
theorem homogeneousSymmetric_ext {σ R : Type*} [CommSemiring R] [Infinite σ]
    {n : ℕ} {f g : symmetricFunctionGrading σ R n}
    (h : ∀ μ : Nat.Partition n,
      coeff (monomialRepresentative σ μ.toAllPartitions) (f : MvPowerSeries σ R) =
        coeff (monomialRepresentative σ μ.toAllPartitions) (g : MvPowerSeries σ R)) : f = g := by
  have hf : IsHomogeneous (f : MvPowerSeries σ R) n := symmetricFunctionGrading.isHomogeneous f
  have hg : IsHomogeneous (g : MvPowerSeries σ R) n := symmetricFunctionGrading.isHomogeneous g
  apply symmetricFunctionGrading.ext
  ext m
  by_cases hm : m.toAllPartitions.size = n
  · rw [coeff_of_isSymmetric m (f : MvPowerSeries σ R) (symmetricFunctionGrading.isSymmetric f),
      coeff_of_isSymmetric m (g : MvPowerSeries σ R) (symmetricFunctionGrading.isSymmetric g)]
    simpa only [AllPartitions.toAllPartitions_toPartition] using
      h (m.toAllPartitions.toPartition hm)
  · exact (hf.coeff_eq_zero hm).trans (hg.coeff_eq_zero hm).symm

section MonomialSymmetric
variable (σ R : Type*) [CommSemiring R] {n : ℕ} (μ : Nat.Partition n)

/-- The monomial symmetric power series indexed by a partition of `n`. -/
def msymm : MvPowerSeries σ R :=
  fun (m : σ →₀ ℕ) =>
    if m.toAllPartitions = μ.toAllPartitions then 1 else 0

theorem isHomogeneous_msymm : IsHomogeneous (msymm σ R μ) n := by
  intro m hm
  change (if m.toAllPartitions = μ.toAllPartitions then 1 else 0 : R) ≠ 0 at hm
  split_ifs at hm with h
  · rw [← m.toAllPartitions_size, h, Nat.Partition.size_toAllPartitions]
  · exact (hm rfl).elim

@[simp]
lemma coeff_msymm {σ R : Type*} [CommSemiring R]
    (μ : Nat.Partition n) (m : σ →₀ ℕ) :
    coeff m (msymm σ R μ) = if m.toAllPartitions = μ.toAllPartitions then 1 else 0 := rfl

/-- Reading a monomial symmetric function at a chosen representative gives a delta coefficient. -/
@[simp]
theorem coeff_monomialRepresentative_msymm {σ R : Type*} [CommSemiring R] [Infinite σ]
    (μ : AllPartitions) (ν : Nat.Partition n) :
    coeff (monomialRepresentative σ μ) (msymm σ R ν) =
      if μ = ν.toAllPartitions then 1 else 0 := by
  rw [coeff_msymm, monomialRepresentative_toAllPartitions]

theorem isSymmetric_msymm : IsSymmetric (msymm σ R μ) := by
  intro e
  ext m
  simp [renameEquiv_coeff]

lemma msymm_mem_symmetricFunctionSubalgebra :
    msymm σ R μ ∈ symmetricFunctionSubalgebra σ R :=
  mem_symmetricFunctionSubalgebra_of_isHomogeneous
    (isHomogeneous_msymm σ R μ) (isSymmetric_msymm σ R μ)

/-- A monomial symmetric function as an element of the degree-`n` piece of the
symmetric-function algebra. -/
def msymmGraded : symmetricFunctionGrading σ R n :=
  symmetricFunctionGrading.mk (msymm σ R μ)
    (isHomogeneous_msymm σ R μ) (isSymmetric_msymm σ R μ)

@[simp]
theorem coe_msymmGraded :
    (msymmGraded σ R μ : MvPowerSeries σ R) = msymm σ R μ :=
  rfl

/-- Homogeneous symmetric series of degree `n`, identified with their monomial symmetric
coordinates. Each coordinate can be read at any exponent vector with the corresponding
partition, as expressed by `msymmEquivFun_apply_eq_coeff`. -/
def msymmEquivFun [Infinite σ] (n : ℕ) :
    symmetricFunctionGrading σ R n ≃ₗ[R] (Nat.Partition n → R) where
  toLinearMap := LinearMap.pi fun μ =>
    (coeff (monomialRepresentative σ μ.toAllPartitions)).comp
      (symmetricFunctionGradingToMvPowerSeries σ R n)
  invFun g := ∑ μ : Nat.Partition n,
    (g μ) • msymmGraded σ R μ
  left_inv p := by
    apply homogeneousSymmetric_ext
    intro μ
    simp
  right_inv g := by
    ext μ
    simp

@[simp]
theorem msymmEquivFun_apply [Infinite σ] {n : ℕ}
    (f : symmetricFunctionGrading σ R n) (μ : Nat.Partition n) :
    msymmEquivFun σ R n f μ = coeff (monomialRepresentative σ μ.toAllPartitions) f := rfl

/-- The monomial symmetric coordinate is independent of the choice of representative. -/
theorem msymmEquivFun_apply_eq_coeff [Infinite σ] {n : ℕ}
    (f : symmetricFunctionGrading σ R n) (μ : Nat.Partition n) (m : σ →₀ ℕ)
    (hm : m.toAllPartitions = μ.toAllPartitions) :
    msymmEquivFun σ R n f μ = coeff m f := by
  rw [msymmEquivFun_apply]
  apply coeff_eq_of_toAllPartitions_eq
  · exact symmetricFunctionGrading.isSymmetric f
  · rw [monomialRepresentative_toAllPartitions, hm]

@[simp]
theorem msymmEquivFun_symm_apply [Infinite σ] {n : ℕ} (g : Nat.Partition n → R) :
    (msymmEquivFun σ R n).symm g =
      ∑ μ : Nat.Partition n, (g μ) • msymmGraded σ R μ := rfl

/-- The monomial symmetric basis of the degree-`n` homogeneous symmetric series. -/
def msymm_basis [Infinite σ] (n : ℕ) :
    Module.Basis (Nat.Partition n) R (symmetricFunctionGrading σ R n) :=
  Module.Basis.ofEquivFun (msymmEquivFun σ R n)

@[simp]
theorem msymm_basis_apply [Infinite σ] {n : ℕ} (μ : Nat.Partition n) :
    msymm_basis σ R n μ = msymmGraded σ R μ := by
  simp [msymm_basis, Module.Basis.coe_ofEquivFun, msymmEquivFun_symm_apply, Pi.single_apply]

@[simp]
theorem msymm_basis_repr_apply [Infinite σ] {n : ℕ}
    (f : symmetricFunctionGrading σ R n) (μ : Nat.Partition n) :
    (msymm_basis σ R n).repr f μ = coeff (monomialRepresentative σ μ.toAllPartitions) f := by
  rw [msymm_basis, Module.Basis.ofEquivFun_repr_apply, msymmEquivFun_apply]

/-- Basis coordinates can be computed using any exponent vector with the required partition. -/
theorem msymm_basis_repr_apply_eq_coeff [Infinite σ] {n : ℕ}
    (f : symmetricFunctionGrading σ R n) (μ : Nat.Partition n) (m : σ →₀ ℕ)
    (hm : m.toAllPartitions = μ.toAllPartitions) :
    (msymm_basis σ R n).repr f μ = coeff m f := by
  rw [msymm_basis, Module.Basis.ofEquivFun_repr_apply]
  exact msymmEquivFun_apply_eq_coeff σ R f μ m hm

end MonomialSymmetric

end MvPowerSeries
