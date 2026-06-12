import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.List.ToFinsupp

import SymmetricPoly.MvPowerSeries.HomogeneousSymmetric


noncomputable section

namespace MvPowerSeries

/-- Maps a partition to a finitely supported function on `ℕ` (a `Finsupp`). -/
def canonicalMonomialNat (μ : Partition) : ℕ →₀ ℕ :=
  List.toFinsupp μ.parts

/-- For an infinite type `σ`, have `ℕ ↪ σ`. We can use this turn the
  `ℕ →₀ ℕ` into a `σ →₀ ℕ`. -/
noncomputable def canonicalMonomial (σ : Type*) [Infinite σ] (μ : Partition) : σ →₀ ℕ :=
  (canonicalMonomialNat μ).embDomain (Infinite.natEmbedding σ)
  -- mapDomainEmbedding may also be useful?

theorem canonicalMonomialNat_toPartition (μ : Partition) :
    (canonicalMonomialNat μ).toPartition = μ := by
  apply Partition.ext'.mpr
  rw [Finsupp.toPartition_toMultiset]
  simp only [canonicalMonomialNat]
  unfold Partition.toMultiset
  sorry

theorem canonicalMonomial_toPartition (σ : Type*) [Infinite σ] (μ : Partition) :
    (canonicalMonomial σ μ).toPartition = μ := by
  unfold canonicalMonomial
  rw [Finsupp.embDomain_toPartition]
  exact canonicalMonomialNat_toPartition μ

lemma coeff_eq_of_toPartition_eq {σ R : Type*} [CommSemiring R]
    (m₁ m₂ : σ →₀ ℕ) (f : MvPowerSeries σ R) (hf : f.IsSymmetric)
    (h : m₁.toPartition = m₂.toPartition) :
    coeff m₁ f = coeff m₂ f := by
  obtain ⟨e, rfl⟩ := Finsupp.exists_smul_of_toPartition_eq m₁ m₂ h
  exact coeff_smul_monomial e m₂ f hf


section MonomialSymmetric
variable (σ R : Type*) [CommSemiring R] (μ : Partition)

def msymm : MvPowerSeries σ R :=
  fun (m : σ →₀ ℕ) =>
    if m.toPartition = μ then 1 else 0

theorem msymm_isHomogeneous : IsHomogeneous (msymm σ R μ) |μ| := by
  sorry

theorem msymm_isHomogeneous' (σ R : Type*) [CommSemiring R] (μ : PartitionOf n) :
    IsHomogeneous (msymm σ R μ) n := by
  nth_rw 2 [← μ.property]
  exact msymm_isHomogeneous σ R μ

@[simp]
lemma coeff_msymm {σ R : Type*} [CommSemiring R]
    (μ : Partition) (m : σ →₀ ℕ) :
  coeff m (msymm σ R μ) = if m.toPartition = μ then 1 else 0 := rfl

theorem msymm_isSymmetric : IsSymmetric (msymm σ R μ) := by
  intro e; ext m; simp

-- Lean knows how to handle the intersection of two sub-objects automatically
lemma msymm_mem_homogeneousSymmetricSubmodule :
  msymm σ R μ ∈ homogeneousSymmetricSubmodule σ R |μ| :=
  ⟨msymm_isHomogeneous σ R μ, msymm_isSymmetric σ R μ⟩

lemma msymm_mem_homogeneousSymmetricSubmodule' (σ R : Type*) [CommSemiring R] (μ : PartitionOf n) :
  msymm σ R μ ∈ homogeneousSymmetricSubmodule σ R n :=
  ⟨msymm_isHomogeneous' σ R μ, msymm_isSymmetric σ R μ⟩

def msymm_basis [Infinite σ] (n : ℕ) :
    Module.Basis (PartitionOf n) R (homogeneousSymmetricSubmodule σ R n) :=
  Module.Basis.ofEquivFun
  {
    toFun := fun p => fun (μ : PartitionOf n) => coeff (canonicalMonomial σ μ) p,
    invFun := fun g => ∑ μ : PartitionOf n,
      (g μ) • (⟨msymm σ R μ, msymm_mem_homogeneousSymmetricSubmodule' σ R μ⟩ :
            homogeneousSymmetricSubmodule σ R n),
    left_inv := sorry,
    right_inv := sorry
    map_add' := sorry,
    map_smul' := sorry
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


-- noncomputable def msymmHomogeneousBasis (σ R : Type*) [CommSemiring R] [Infinite σ] (n : ℕ) :
--     Module.Basis (PartitionOf n) R (symmetricHomogeneousSubmodule σ R n) :=
--   Module.Basis.ofEquivFun (msymmEquivFun σ R n)

-- noncomputable def msymmHom (σ R : Type*) [CommSemiring R] (n : ℕ) :
--   (PartitionOf n →₀ R) →ₗ[R] SymmetricFunction σ R :=
--   Finsupp.linearCombination R (fun μ ↦ msymm σ R μ)

-- variable (σ R) [CommSemiring R]
-- /-- The `R`-algebra homomorphism from $R[x_1, x_2, \dots]$ to the algebra of symmetric functions
--   sending $x_i$ to the $i$-th elementary symmetric polynomial. -/
-- noncomputable def esymmAlgHom :
--     MvPolynomial ℕ R →ₐ[R] SymmetricFunction σ R :=
--   MvPolynomial.aeval (fun i ↦ esymm σ R (i + 1))




end MvPowerSeries
