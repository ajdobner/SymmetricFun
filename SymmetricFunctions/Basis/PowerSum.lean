import SymmetricFunctions.Plethysm.Rational
import SymmetricFunctions.Basis.Elementary

/-! # Partition-indexed power-sum bases over rational coefficient algebras

The products themselves exist over every commutative ring. Invertibility of
positive integers is used only for their basis property and evaluation API.
-/

noncomputable section

namespace SymmetricFunction

open SymmetricFunctions

variable {R : Type*} [CommRing R] {d : ℕ}

/-- The product of positive power sums, with each part's multiplicity retained. -/
def pPart (μ : Nat.Partition d) : SymmetricFunction R :=
  (Partition.toExponents μ).prod (fun i k => p i ^ k)

theorem pPart_eq_prod_positiveParts (μ : Nat.Partition d) :
    pPart (R := R) μ = ((Partition.positiveParts μ).map p).prod := by
  classical
  rw [← Partition.toMultiset_toExponents, Finsupp.toMultiset_map, Finsupp.prod_toMultiset]
  exact (Finsupp.prod_mapDomain_index (fun b => pow_zero b)
    (fun b m n => pow_add b m n)).symm

@[simp] theorem pPart_zero (μ : Nat.Partition 0) : pPart (R := R) μ = 1 := by
  simp [pPart]

variable [Algebra ℚ R]

@[simp] theorem powerSumChangeOfGenerators_ePart (μ : Nat.Partition d) :
    powerSumChangeOfGenerators R (ePart μ) = pPart μ := by
  simp [ePart_eq_prod, pPart, Finsupp.prod]

theorem isHomogeneous_pPart (μ : Nat.Partition d) : IsHomogeneous (pPart (R := R) μ) d := by
  rw [← powerSumChangeOfGenerators_ePart]
  exact (isHomogeneous_ePart μ).powerSumChange

/-- The power-sum basis of degree d. -/
def pBasis (R : Type*) [CommRing R] [Algebra ℚ R] (d : ℕ) :
    Module.Basis (Nat.Partition d) R (homogeneousSubmodule R d) :=
  (eBasis R d).map (powerSumHomogeneous R d)

@[simp] theorem pBasis_apply (μ : Nat.Partition d) :
    (pBasis R d μ : SymmetricFunction R) = pPart μ := by simp [pBasis]

theorem pBasis_repr (f : homogeneousSubmodule R d) (μ : Nat.Partition d) :
    (pBasis R d).repr f μ =
      ((powerSumPolynomialEquiv R).symm f).coeff (Partition.toExponents μ) := by
  change (eBasis R d).repr ((powerSumHomogeneous R d).symm f) μ = _
  rw [eBasis_repr, powerSumHomogeneous_symm_apply]
  rfl

/-- The full power-sum basis; every symmetric function has a finite expansion. -/
def pBasisAll (R : Type*) [CommRing R] [Algebra ℚ R] :
    Module.Basis (Σ d, Nat.Partition d) R (SymmetricFunction R) :=
  (eBasisAll R).map (powerSumChangeOfGenerators R).toLinearEquiv

@[simp] theorem pBasisAll_apply (μ : Σ d, Nat.Partition d) :
    pBasisAll R μ = pPart μ.2 := by simp [pBasisAll]

theorem pBasisAll_repr (f : SymmetricFunction R) (μ : Σ d, Nat.Partition d) :
    (pBasisAll R).repr f μ =
      ((powerSumPolynomialEquiv R).symm f).coeff (Partition.toExponents μ.2) := by
  change (eBasisAll R).repr ((powerSumChangeOfGenerators R).symm f) μ = _
  rw [eBasisAll_repr]
  rfl

variable {A : Type*} [CommRing A] [Algebra R A]

theorem powerSumEval_pPart (x : ℕ+ → A) (μ : Nat.Partition d) :
    powerSumEval x (pPart (R := R) μ) =
      (Partition.toExponents μ).prod (fun i k => x i ^ k) := by
  simp [pPart, Finsupp.prod]

end SymmetricFunction
