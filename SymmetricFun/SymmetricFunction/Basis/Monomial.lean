module

public import Mathlib.Data.List.ToFinsupp
public import Mathlib.LinearAlgebra.Basis.Defs
public import SymmetricFun.SymmetricFunction.Basis.Defs

/-!
# The monomial symmetric basis and its coordinates

The monomial symmetric functions are defined in `SymmetricFunction/Basis/Defs`.
Chosen exponent representatives let `msymmPartEquivFun` read the coordinates of
a homogeneous symmetric series; `msymmPartEquivFun_apply_eq_coeff` allows any exponent
vector with the required partition to be used instead.

The coordinate construction uses the fact that exponent vectors with the same
partition differ by a permutation.

`msymmPart_basis` is a basis of the internal degree-`n` piece of the symmetric-function
algebra. Its vectors are `msymmPartGraded`, and its coordinates are described by
`msymmPart_basis_repr_apply`.
-/

@[expose] public section
noncomputable section

namespace MvPowerSeries

/-! ## Representatives and coordinates -/

/-- A chosen exponent vector on `ℕ` with the given partition.
The ordering supplied by `Multiset.toList` is an implementation choice. -/
def monomialRepresentativeNat (μ : IntegerPartition) : ℕ →₀ ℕ :=
  List.toFinsupp μ.parts.toList

/-- A chosen exponent vector with the given partition in an infinite set of variables.
The embedding of `ℕ` into `σ` is an implementation choice. Use
`monomialRepresentative_toIntegerPartition` to work with its partition. -/
noncomputable def monomialRepresentative (σ : Type*) [Infinite σ] (μ : IntegerPartition) : σ →₀ ℕ :=
  (monomialRepresentativeNat μ).embDomain (Infinite.natEmbedding σ)

@[simp]
theorem monomialRepresentativeNat_toIntegerPartition (μ : IntegerPartition) :
    (monomialRepresentativeNat μ).toIntegerPartition = μ := by
  apply IntegerPartition.ext
  let l := μ.parts.toList
  have hs : l.toFinsupp.support = Finset.range l.length := by
    rw [List.toFinsupp_support]
    apply Finset.filter_eq_self.mpr
    intro i hi
    rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hi)]
    exact (μ.parts_pos (Multiset.mem_toList.mp
      (List.getElem_mem (l := l) (Finset.mem_range.mp hi)))).ne'
  have hl : (List.range l.length).map (l.getD · 0) = l := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_range]
      exact List.getD_eq_getElem _ _ hi'
  change l.toFinsupp.support.val.map l.toFinsupp = μ.parts
  rw [hs]
  change ((List.range l.length).map (l.getD · 0) : Multiset ℕ) = μ.parts
  rw [hl]
  exact Multiset.coe_toList μ.parts

@[simp]
theorem monomialRepresentative_toIntegerPartition (σ : Type*) [Infinite σ] (μ : IntegerPartition) :
    (monomialRepresentative σ μ).toIntegerPartition = μ := by
  unfold monomialRepresentative
  rw [Finsupp.embDomain_toIntegerPartition]
  exact monomialRepresentativeNat_toIntegerPartition μ

lemma coeff_eq_of_toIntegerPartition_eq {σ R : Type*} [CommSemiring R]
    (m₁ m₂ : σ →₀ ℕ) (f : MvPowerSeries σ R) (hf : f.IsSymmetric)
    (h : m₁.toIntegerPartition = m₂.toIntegerPartition) :
    coeff m₁ f = coeff m₂ f := by
  obtain ⟨e, rfl⟩ := Finsupp.exists_equivMapDomain_of_toIntegerPartition_eq m₁ m₂ h
  exact coeff_equivMapDomain_of_isSymmetric e m₂ f hf

theorem coeff_of_isSymmetric {σ R : Type*} [CommSemiring R] [Infinite σ]
    (m : σ →₀ ℕ) (f : MvPowerSeries σ R) (hf : f.IsSymmetric) :
    coeff m f = coeff (monomialRepresentative σ m.toIntegerPartition) f :=
  coeff_eq_of_toIntegerPartition_eq m _ f hf
    (monomialRepresentative_toIntegerPartition σ m.toIntegerPartition).symm

/-- Homogeneous symmetric series are determined by one coefficient per partition of their degree. -/
theorem homogeneousSymmetric_ext {σ R : Type*} [CommSemiring R] [Infinite σ]
    {n : ℕ} {f g : symmetricFunctionGrading σ R n}
    (h : ∀ μ : Nat.Partition n,
      coeff (monomialRepresentative σ μ.toIntegerPartition) (f : MvPowerSeries σ R) =
        coeff (monomialRepresentative σ μ.toIntegerPartition) (g : MvPowerSeries σ R)) : f = g := by
  have hf : IsHomogeneous (f : MvPowerSeries σ R) n := symmetricFunctionGrading.isHomogeneous f
  have hg : IsHomogeneous (g : MvPowerSeries σ R) n := symmetricFunctionGrading.isHomogeneous g
  apply symmetricFunctionGrading.ext
  ext m
  by_cases hm : m.toIntegerPartition.size = n
  · rw [coeff_of_isSymmetric m (f : MvPowerSeries σ R) (symmetricFunctionGrading.isSymmetric f),
      coeff_of_isSymmetric m (g : MvPowerSeries σ R) (symmetricFunctionGrading.isSymmetric g)]
    simpa only [IntegerPartition.toIntegerPartition_toPartition] using
      h (m.toIntegerPartition.toPartition hm)
  · exact (hf.coeff_eq_zero hm).trans (hg.coeff_eq_zero hm).symm

/-- Reading a monomial symmetric function at a chosen representative gives a delta coefficient. -/
@[simp]
theorem coeff_monomialRepresentative_msymmPart {σ R : Type*} [CommSemiring R] [Infinite σ]
    {n : ℕ} (μ : IntegerPartition) (ν : Nat.Partition n) :
    coeff (monomialRepresentative σ μ) (msymmPart σ R ν) =
      if μ = ν.toIntegerPartition then 1 else 0 := by
  rw [coeff_msymmPart, monomialRepresentative_toIntegerPartition]

section MonomialBasis
variable (σ R : Type*) [CommSemiring R]

/-- Homogeneous symmetric series of degree `n`, identified with their monomial symmetric
coordinates. Each coordinate can be read at any exponent vector with the corresponding
partition, as expressed by `msymmPartEquivFun_apply_eq_coeff`. -/
def msymmPartEquivFun [Infinite σ] (n : ℕ) :
    symmetricFunctionGrading σ R n ≃ₗ[R] (Nat.Partition n → R) where
  toLinearMap := LinearMap.pi fun μ =>
    (coeff (monomialRepresentative σ μ.toIntegerPartition)).comp
      (symmetricFunctionGradingToMvPowerSeries σ R n)
  invFun g := ∑ μ : Nat.Partition n,
    (g μ) • msymmPartGraded σ R μ
  left_inv p := by
    apply homogeneousSymmetric_ext
    intro μ
    simp
  right_inv g := by
    ext μ
    simp

@[simp]
theorem msymmPartEquivFun_apply [Infinite σ] {n : ℕ}
    (f : symmetricFunctionGrading σ R n) (μ : Nat.Partition n) :
    msymmPartEquivFun σ R n f μ = coeff (monomialRepresentative σ μ.toIntegerPartition) f := rfl

/-- The monomial symmetric coordinate is independent of the choice of representative. -/
theorem msymmPartEquivFun_apply_eq_coeff [Infinite σ] {n : ℕ}
    (f : symmetricFunctionGrading σ R n) (μ : Nat.Partition n) (m : σ →₀ ℕ)
    (hm : m.toIntegerPartition = μ.toIntegerPartition) :
    msymmPartEquivFun σ R n f μ = coeff m f := by
  rw [msymmPartEquivFun_apply]
  apply coeff_eq_of_toIntegerPartition_eq
  · exact symmetricFunctionGrading.isSymmetric f
  · rw [monomialRepresentative_toIntegerPartition, hm]

@[simp]
theorem msymmPartEquivFun_symm_apply [Infinite σ] {n : ℕ} (g : Nat.Partition n → R) :
    (msymmPartEquivFun σ R n).symm g =
      ∑ μ : Nat.Partition n, (g μ) • msymmPartGraded σ R μ := rfl

/-- The monomial symmetric basis of the degree-`n` homogeneous symmetric series. -/
def msymmPart_basis [Infinite σ] (n : ℕ) :
    Module.Basis (Nat.Partition n) R (symmetricFunctionGrading σ R n) :=
  Module.Basis.ofEquivFun (msymmPartEquivFun σ R n)

@[simp]
theorem msymmPart_basis_apply [Infinite σ] {n : ℕ} (μ : Nat.Partition n) :
    msymmPart_basis σ R n μ = msymmPartGraded σ R μ := by
  simp [msymmPart_basis, Module.Basis.coe_ofEquivFun, msymmPartEquivFun_symm_apply, Pi.single_apply]

@[simp]
theorem msymmPart_basis_repr_apply [Infinite σ] {n : ℕ}
    (f : symmetricFunctionGrading σ R n) (μ : Nat.Partition n) :
    (msymmPart_basis σ R n).repr f μ = coeff (monomialRepresentative σ μ.toIntegerPartition) f := by
  rw [msymmPart_basis, Module.Basis.ofEquivFun_repr_apply, msymmPartEquivFun_apply]

/-- Basis coordinates can be computed using any exponent vector with the required partition. -/
theorem msymmPart_basis_repr_apply_eq_coeff [Infinite σ] {n : ℕ}
    (f : symmetricFunctionGrading σ R n) (μ : Nat.Partition n) (m : σ →₀ ℕ)
    (hm : m.toIntegerPartition = μ.toIntegerPartition) :
    (msymmPart_basis σ R n).repr f μ = coeff m f := by
  rw [msymmPart_basis, Module.Basis.ofEquivFun_repr_apply]
  exact msymmPartEquivFun_apply_eq_coeff σ R f μ m hm

end MonomialBasis

end MvPowerSeries
