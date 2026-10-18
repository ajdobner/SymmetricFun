module

public import SymmetricFun.SymmetricFunction.Basis.Defs
public import SymmetricFun.SymmetricFunction.Basis.Monomial
public import SymmetricFun.Tableau.KostkaDominance

/-!
# Schur expansions in monomial symmetric functions

Ordinary and skew Schur functions expand in monomial symmetric functions with
Kostka coefficients. These formulas hold over a commutative semiring for any
variable type. The skew expansion uses `hd : n = m + d` to specify its degree.
For infinitely many variables, the monomial basis coordinates are Kostka numbers:
they vanish outside dominance and equal one on the diagonal.
-/

@[expose] public section
noncomputable section

namespace MvPowerSeries

variable (σ R : Type*) [CommSemiring R]

/-- The monomial symmetric expansion of a skew Schur function in its specified degree. -/
theorem skewSsymmPart_eq_sum_msymmPart {n m d : ℕ}
    (π : Nat.Partition n) (μ : Nat.Partition m) (hd : n = m + d) :
    skewSsymmPart σ R π μ =
      ∑ ν : Nat.Partition d, (Nat.Partition.skewKostka π μ ν : R) • msymmPart σ R ν := by
  classical
  ext a
  simp only [map_sum, coeff_smul, coeff_msymmPart]
  by_cases ha : a.toIntegerPartition.size = d
  · let ν : Nat.Partition d := a.toIntegerPartition.toPartition ha
    have hp : a.toIntegerPartition = ν.toIntegerPartition :=
      (IntegerPartition.toIntegerPartition_toPartition _ ha).symm
    rw [coeff_skewSsymmPart, hp]
    simp [Nat.Partition.toIntegerPartition_inj]
    rfl
  · have hdegree : a.degree ≠ d := ha
    rw [IsHomogeneous.coeff_eq_zero (isHomogeneous_skewSsymmPart σ R π μ hd) hdegree]
    symm
    apply Finset.sum_eq_zero
    intro ν _
    have hp : a.toIntegerPartition ≠ ν.toIntegerPartition := by
      intro h
      apply ha
      simpa using congrArg IntegerPartition.size h
    simp [hp]

/-- The monomial symmetric expansion of an ordinary Schur function. -/
theorem ssymmPart_eq_sum_msymmPart {n : ℕ} (π : Nat.Partition n) :
    ssymmPart σ R π =
      ∑ ν : Nat.Partition n, (Nat.Partition.kostka π ν : R) • msymmPart σ R ν :=
  skewSsymmPart_eq_sum_msymmPart σ R π (default : Nat.Partition 0) (by simp)

/-- The Schur-to-monomial transition coefficients are the Kostka numbers. -/
theorem msymmPart_basis_repr_ssymmPartGraded [Infinite σ] {n : ℕ}
    (π μ : Nat.Partition n) :
    (msymmPart_basis σ R n).repr (ssymmPartGraded σ R π) μ =
      (Nat.Partition.kostka π μ : R) := by
  rw [msymmPart_basis_repr_apply]
  change coeff (monomialRepresentative σ μ.toIntegerPartition) (ssymmPart σ R π) = _
  rw [coeff_ssymmPart, monomialRepresentative_toIntegerPartition]
  rfl

/-- A Schur function has no monomial term outside the dominance bound. -/
theorem msymmPart_basis_repr_ssymmPartGraded_eq_zero [Infinite σ] {n : ℕ}
    (π μ : Nat.Partition n) (h : ¬ π.Dominates μ) :
    (msymmPart_basis σ R n).repr (ssymmPartGraded σ R π) μ = 0 := by
  rw [msymmPart_basis_repr_ssymmPartGraded, Nat.Partition.kostka_eq_zero_of_not_dominates π μ h,
    Nat.cast_zero]

/-- The leading monomial coefficient of a Schur function is one. -/
@[simp]
theorem msymmPart_basis_repr_ssymmPartGraded_self [Infinite σ] {n : ℕ}
    (π : Nat.Partition n) :
    (msymmPart_basis σ R n).repr (ssymmPartGraded σ R π) π = 1 := by
  rw [msymmPart_basis_repr_ssymmPartGraded, Nat.Partition.kostka_self, Nat.cast_one]

end MvPowerSeries
