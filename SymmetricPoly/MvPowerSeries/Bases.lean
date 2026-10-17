import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.List.ToFinsupp

import SymmetricPoly.MvPowerSeries.HomogeneousSymmetric


noncomputable section

namespace MvPowerSeries

/-- Maps a partition to a finitely supported function on `ℕ` (a `Finsupp`). -/
def canonicalMonomialNat (μ : AllPartitions) : ℕ →₀ ℕ :=
  List.toFinsupp μ.parts.toList

/-- For an infinite type `σ`, have `ℕ ↪ σ`. We can use this turn the
  `ℕ →₀ ℕ` into a `σ →₀ ℕ`. -/
noncomputable def canonicalMonomial (σ : Type*) [Infinite σ] (μ : AllPartitions) : σ →₀ ℕ :=
  (canonicalMonomialNat μ).embDomain (Infinite.natEmbedding σ)

theorem canonicalMonomialNat_toAllPartitions (μ : AllPartitions) :
    (canonicalMonomialNat μ).toAllPartitions = μ := by
  sorry

theorem canonicalMonomial_toAllPartitions (σ : Type*) [Infinite σ] (μ : AllPartitions) :
    (canonicalMonomial σ μ).toAllPartitions = μ := by
  unfold canonicalMonomial
  rw [Finsupp.embDomain_toAllPartitions]
  exact canonicalMonomialNat_toAllPartitions μ

lemma coeff_eq_of_toAllPartitions_eq {σ R : Type*} [CommSemiring R]
    (m₁ m₂ : σ →₀ ℕ) (f : MvPowerSeries σ R) (hf : f.IsSymmetric)
    (h : m₁.toAllPartitions = m₂.toAllPartitions) :
    coeff m₁ f = coeff m₂ f := by
  obtain ⟨e, rfl⟩ := Finsupp.exists_equivMapDomain_of_toAllPartitions_eq m₁ m₂ h
  exact coeff_equivMapDomain_of_isSymmetric e m₂ f hf

theorem coeff_of_isSymmetric {σ R : Type*} [CommSemiring R] [Infinite σ]
  (m : σ →₀ ℕ) (f : MvPowerSeries σ R) (hf : f.IsSymmetric) :
    coeff m f = coeff (canonicalMonomial σ m.toAllPartitions) f := by
  rw [← coeff_eq_of_toAllPartitions_eq m (canonicalMonomial σ m.toAllPartitions) f hf]
  rw [canonicalMonomial_toAllPartitions]


section MonomialSymmetric
variable (σ R : Type*) [CommSemiring R] (μ : AllPartitions)

def msymm : MvPowerSeries σ R :=
  fun (m : σ →₀ ℕ) =>
    if m.toAllPartitions = μ then 1 else 0

theorem isHomogeneous_msymm : IsHomogeneous (msymm σ R μ) μ.size := by
  intro m hm
  change (if m.toAllPartitions = μ then 1 else 0 : R) ≠ 0 at hm
  split_ifs at hm with h
  · rw [← m.toAllPartitions_size, h]
  · exact (hm rfl).elim

theorem isHomogeneous_msymm' (σ R : Type*) [CommSemiring R] (μ : Nat.Partition n) :
    IsHomogeneous (msymm σ R μ.toAllPartitions) n :=
  isHomogeneous_msymm σ R μ.toAllPartitions

@[simp]
lemma coeff_msymm {σ R : Type*} [CommSemiring R]
    (μ : AllPartitions) (m : σ →₀ ℕ) :
  coeff m (msymm σ R μ) = if m.toAllPartitions = μ then 1 else 0 := rfl

theorem isSymmetric_msymm : IsSymmetric (msymm σ R μ) := by
  intro e
  ext m
  simp [renameEquiv_coeff]

lemma msymm_mem_homogeneousSymmetricSubmodule :
  msymm σ R μ ∈ homogeneousSymmetricSubmodule σ R μ.size :=
  ⟨isHomogeneous_msymm σ R μ, isSymmetric_msymm σ R μ⟩

lemma msymm_mem_homogeneousSymmetricSubmodule' (σ R : Type*) [CommSemiring R]
    (μ : Nat.Partition n) : msymm σ R μ.toAllPartitions ∈ homogeneousSymmetricSubmodule σ R n :=
  ⟨isHomogeneous_msymm' σ R μ, isSymmetric_msymm σ R μ.toAllPartitions⟩

def msymm_basis [Infinite σ] (n : ℕ) :
    Module.Basis (Nat.Partition n) R (homogeneousSymmetricSubmodule σ R n) :=
  Module.Basis.ofEquivFun
  {
    toFun := fun p => fun (μ : Nat.Partition n) =>
      coeff (canonicalMonomial σ μ.toAllPartitions) p,
    invFun := fun g => ∑ μ : Nat.Partition n,
      (g μ) • (⟨msymm σ R μ.toAllPartitions, msymm_mem_homogeneousSymmetricSubmodule' σ R μ⟩ :
            homogeneousSymmetricSubmodule σ R n),
    left_inv := by
      intro p
      ext m
      simp only [SetLike.mk_smul_mk, AddSubmonoidClass.coe_finsetSum, map_sum, map_smul,
        coeff_msymm, smul_eq_mul, mul_ite, mul_one, mul_zero]
      by_cases hm : (m.toAllPartitions.size = n)
      · let m_part : Nat.Partition n := m.toAllPartitions.toPartition hm
        have hpart (x : Nat.Partition n) :
            m.toAllPartitions = x.toAllPartitions ↔ m_part = x := by
          rw [AllPartitions.ext_iff, Nat.Partition.ext_iff]
          rfl
        simp_rw [hpart]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, m_part,
          AllPartitions.toAllPartitions_toPartition]
        rw [← coeff_of_isSymmetric m _ _]
        exact ((mem_homogeneousSymmetricSubmodule n ↑p.val).mp p.property).2
      · transitivity 0
        · apply Finset.sum_eq_zero
          intro x hx
          simp only [ite_eq_right_iff]
          intro heq
          exfalso
          apply hm
          rw [heq]
          rfl
        · symm
          revert hm
          contrapose
          rw [m.toAllPartitions_size]
          exact ((mem_homogeneousSymmetricSubmodule n ↑p.val).mp p.property).1
      ,
    right_inv := by
      intro g
      ext μ
      simp only [SetLike.mk_smul_mk, AddSubmonoidClass.coe_finsetSum, map_sum, map_smul,
        coeff_msymm, smul_eq_mul, mul_ite, mul_one, mul_zero, canonicalMonomial_toAllPartitions,
        Nat.Partition.toAllPartitions_inj, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]
    map_add' := by
      intro g₁ g₂
      ext μ
      simp
    ,
    map_smul' := by
      intro r g
      ext μ
      simp
  }

end MonomialSymmetric

section ElementarySymmetric
variable (σ R : Type*) [CommSemiring R]

def esymmMvPowerSeries (n : ℕ) : MvPowerSeries σ R :=
  fun c ↦ if c.support.card = n ∧ (∀ i ∈ c.support, c i = 1) then 1 else 0

end ElementarySymmetric

section HomogeneousSymmetric
variable (σ R : Type*) [CommSemiring R]

def hsymmMvPowerSeries (n : ℕ) : MvPowerSeries σ R :=
  fun c ↦ if c.degree = n then 1 else 0

end HomogeneousSymmetric

end MvPowerSeries
