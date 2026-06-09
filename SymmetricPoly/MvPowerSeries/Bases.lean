import SymmetricPoly.MvPowerSeries.SymmetricFunction
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.List.ToFinsupp

namespace MvPowerSeries

/-- Maps a partition to a finitely supported function on `ℕ` (a `Finsupp`). -/
def canonicalMonomialNat (μ : Partition) : ℕ →₀ ℕ :=
  List.toFinsupp μ.parts

/-- For an infinite type `σ`, have `ℕ ↪ σ`. We can use this turn the
  `ℕ →₀ ℕ` into a `σ →₀ ℕ`. -/
noncomputable def canonicalMonomial (σ : Type*) [Infinite σ] (μ : Partition) : σ →₀ ℕ :=
  (canonicalMonomialNat μ).embDomain (Infinite.natEmbedding σ)
  -- mapDomainEmbedding may also be useful?

lemma coeff_eq_of_toPartition_eq {σ R : Type*} [CommSemiring R]
    (m₁ m₂ : σ →₀ ℕ) (f : MvPowerSeries σ R) (hf : f.IsSymmetric)
    (h : m₁.toPartition = m₂.toPartition) :
    coeff m₁ f = coeff m₂ f := by
  obtain ⟨e, rfl⟩ := Finsupp.exists_smul_of_toPartition_eq m₁ m₂ h
  exact (coeff_smul_monomial e m₁ f hf).symm

end MvPowerSeries

namespace SymmetricFunction

def msymmEquivFun (σ R : Type*) [CommSemiring R] [Infinite σ] (n : ℕ) :
    symmetricHomogeneousSubmodule σ R n ≃ₗ[R] (PartitionOf n → R) := sorry

noncomputable def msymmHomogeneousBasis (σ R : Type*) [CommSemiring R] [Infinite σ] (n : ℕ) :
    Module.Basis (PartitionOf n) R (symmetricHomogeneousSubmodule σ R n) :=
  Module.Basis.ofEquivFun (msymmEquivFun σ R n)

noncomputable def msymmHom (σ R : Type*) [CommSemiring R] (n : ℕ) :
  (PartitionOf n →₀ R) →ₗ[R] SymmetricFunction σ R :=
  Finsupp.linearCombination R (fun μ ↦ msymm σ R μ)

variable (σ R) [CommSemiring R]
/-- The `R`-algebra homomorphism from $R[x_1, x_2, \dots]$ to the algebra of symmetric functions
  sending $x_i$ to the $i$-th elementary symmetric polynomial. -/
noncomputable def esymmAlgHom :
    MvPolynomial ℕ R →ₐ[R] SymmetricFunction σ R :=
  MvPolynomial.aeval (fun i ↦ esymm σ R (i + 1))



end SymmetricFunction
