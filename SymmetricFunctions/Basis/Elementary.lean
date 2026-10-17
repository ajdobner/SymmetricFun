import SymmetricFunctions.Grading
import SymmetricFunctions.Partition
import Mathlib.LinearAlgebra.DirectSum.Basis

/-!
# Elementary partition bases

The weighted monomial basis and its partition indexing were proposed in
ajdobner/SymmetricFun, `SymmetricPoly/SymmFunc/Basic.lean` at commit
98938de95a12b3ed363653cb980588e2a9188cb8. Here they are reconstructed from
Mathlib's supported-polynomial basis and the proved Mathlib partition adapter.
No inherited draft module is imported.
-/

noncomputable section

open scoped BigOperators DirectSum

namespace SymmetricFunctions

/-- The monomial basis of a weighted homogeneous piece, for arbitrary weights. -/
def weightedMonomialBasis (σ R M : Type*) [CommSemiring R] [AddCommMonoid M]
    (w : σ → M) (d : M) :
    Module.Basis {a : σ →₀ ℕ // a.weight w = d} R
      (MvPolynomial.weightedHomogeneousSubmodule R w d) :=
  (MvPolynomial.basisRestrictSupport R {a : σ →₀ ℕ | a.weight w = d}).map
    (LinearEquiv.ofEq _ _ (MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported
      R w d).symm)

@[simp] theorem weightedMonomialBasis_apply (σ R M : Type*) [CommSemiring R]
    [AddCommMonoid M] (w : σ → M) (d : M) (a : {a : σ →₀ ℕ // a.weight w = d}) :
    (weightedMonomialBasis σ R M w d a : MvPolynomial σ R) = MvPolynomial.monomial a.val 1 := by
  change AddMonoidAlgebra.ofCoeff
    (((Finsupp.supportedEquivFinsupp (R := R) {a : σ →₀ ℕ | a.weight w = d}).symm
      (Finsupp.single a 1)).val) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

@[simp] theorem weightedMonomialBasis_repr (σ R M : Type*) [CommSemiring R]
    [AddCommMonoid M] (w : σ → M) (d : M)
    (f : MvPolynomial.weightedHomogeneousSubmodule R w d)
    (a : {a : σ →₀ ℕ // a.weight w = d}) :
    (weightedMonomialBasis σ R M w d).repr f a = f.val.coeff a.val := by
  rfl

namespace Partition

/-- Concatenate the parts of two partitions. -/
def union {m n : ℕ} (μ : Nat.Partition m) (ν : Nat.Partition n) : Nat.Partition (m + n) where
  parts := μ.parts + ν.parts
  parts_pos := by
    intro i hi
    rcases Multiset.mem_add.mp hi with hi | hi
    · exact μ.parts_pos hi
    · exact ν.parts_pos hi
  parts_sum := by simp [μ.parts_sum, ν.parts_sum]

@[simp] theorem union_parts {m n : ℕ} (μ : Nat.Partition m) (ν : Nat.Partition n) :
    (union μ ν).parts = μ.parts + ν.parts := rfl

@[simp] theorem toExponents_union {m n : ℕ} (μ : Nat.Partition m) (ν : Nat.Partition n) :
    toExponents (union μ ν) = toExponents μ + toExponents ν := by
  ext i
  simp

end Partition
end SymmetricFunctions

namespace SymmetricFunction

open SymmetricFunctions

variable {R : Type*} [CommSemiring R] {d : ℕ}

/-- The product of elementary functions indexed by the parts of a partition. -/
def ePart (μ : Nat.Partition d) : SymmetricFunction R := (μ.parts.map e).prod

theorem ePart_eq_prod (μ : Nat.Partition d) :
    ePart (R := R) μ = (Partition.toExponents μ).prod (fun i k => e i ^ k) :=
  Partition.prod_parts μ e

@[simp] theorem polynomialEquiv_ePart (μ : Nat.Partition d) :
    polynomialEquiv R (ePart μ) = MvPolynomial.monomial (Partition.toExponents μ) 1 := by
  rw [ePart_eq_prod, Finsupp.prod]
  simp only [map_prod, map_pow, polynomialEquiv_e]
  exact MvPolynomial.prod_X_pow_eq_monomial

theorem isHomogeneous_ePart (μ : Nat.Partition d) : IsHomogeneous (ePart (R := R) μ) d := by
  unfold IsHomogeneous
  rw [polynomialEquiv_ePart]
  exact MvPolynomial.isWeightedHomogeneous_monomial _ _ _ (Partition.finsupp_weight_toExponents μ)

@[simp] theorem ePart_zero (μ : Nat.Partition 0) : ePart (R := R) μ = 1 := by
  simp [ePart]

theorem ePart_mul {m n : ℕ} (μ : Nat.Partition m) (ν : Nat.Partition n) :
    ePart (R := R) μ * ePart ν = ePart (Partition.union μ ν) := by
  simp [ePart]

/-- Restrict the polynomial presentation to a homogeneous piece. -/
def homogeneousPolynomialEquiv (R : Type*) [CommSemiring R] (d : ℕ) :
    homogeneousSubmodule R d ≃ₗ[R]
      MvPolynomial.weightedHomogeneousSubmodule R (fun i : ℕ+ => (i : ℕ)) d :=
  (polynomialEquiv R).toLinearEquiv.ofSubmodule' _

@[simp] theorem homogeneousPolynomialEquiv_apply (f : homogeneousSubmodule R d) :
    (homogeneousPolynomialEquiv R d f : MvPolynomial ℕ+ R) = polynomialEquiv R f := rfl

@[simp] theorem homogeneousPolynomialEquiv_symm_apply
    (f : MvPolynomial.weightedHomogeneousSubmodule R (fun i : ℕ+ => (i : ℕ)) d) :
    ((homogeneousPolynomialEquiv R d).symm f : SymmetricFunction R) =
      (polynomialEquiv R).symm f := rfl

/-- The elementary basis of the homogeneous piece of degree `d`. -/
def eBasis (R : Type*) [CommSemiring R] (d : ℕ) :
    Module.Basis (Nat.Partition d) R (homogeneousSubmodule R d) :=
  ((weightedMonomialBasis ℕ+ R ℕ (fun i => (i : ℕ)) d).map
    (homogeneousPolynomialEquiv R d).symm).reindex (Partition.weightedExponentEquiv d).symm

@[simp] theorem eBasis_apply (μ : Nat.Partition d) :
    (eBasis R d μ : SymmetricFunction R) = ePart μ := by
  apply (polynomialEquiv R).injective
  simp [eBasis, Module.Basis.reindex_apply]

theorem eBasis_repr (f : homogeneousSubmodule R d) (μ : Nat.Partition d) :
    (eBasis R d).repr f μ = (polynomialEquiv R f).coeff (Partition.toExponents μ) := by
  simp [eBasis]

/-- The full elementary basis, obtained from the direct sum of the homogeneous bases. -/
def eBasisAll (R : Type*) [CommSemiring R] :
    Module.Basis (Σ d, Nat.Partition d) R (SymmetricFunction R) :=
  (DFinsupp.basis (eBasis R)).map (decompose R).symm.toLinearEquiv

theorem eBasisAll_repr (f : SymmetricFunction R) (μ : Σ d, Nat.Partition d) :
    (eBasisAll R).repr f μ = (polynomialEquiv R f).coeff (Partition.toExponents μ.2) := by
  change (eBasis R μ.1).repr (decompose R f μ.1) μ.2 = _
  rw [eBasis_repr]
  change (polynomialEquiv R (homogeneousComponent μ.1 f)).coeff _ = _
  rw [polynomialEquiv_homogeneousComponent]
  simp [MvPolynomial.coeff_weightedHomogeneousComponent, Partition.finsupp_weight_toExponents]

@[simp] theorem eBasisAll_apply (μ : Σ d, Nat.Partition d) :
    eBasisAll R μ = ePart μ.2 := by
  rw [eBasisAll, Module.Basis.map_apply]
  have h : DFinsupp.basis (eBasis R) μ =
      DirectSum.lof R ℕ (fun d => homogeneousSubmodule R d) μ.1 (eBasis R μ.1 μ.2) := by
    simp [DFinsupp.basis, Module.Basis.coe_ofRepr]
    rfl
  rw [h]
  exact (DirectSum.decomposeLinearEquiv_symm_lof (homogeneousSubmodule R) _ _).trans
    (eBasis_apply μ.2)

section Examples

attribute [local irreducible] SymmetricFunction

example : eBasisAll R ⟨0, default⟩ = 1 := by simp

example : eBasisAll R ⟨2, Nat.Partition.indiscrete 2⟩ = e 2 := by
  simp [ePart]

example {m n : ℕ} (μ : Nat.Partition m) (ν : Nat.Partition n) :
    eBasisAll R ⟨m, μ⟩ * eBasisAll R ⟨n, ν⟩ =
      eBasisAll R ⟨m + n, Partition.union μ ν⟩ := by
  simp [ePart_mul]

end Examples

end SymmetricFunction
