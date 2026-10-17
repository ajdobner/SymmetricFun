import SymmetricFun.SymmetricFunction.FundamentalTheorem
import SymmetricFun.SymmetricFunction.Complete
import SymmetricFunctions.Realization.PowerSeries
import SymmetricFunctions.Finite.CompleteCoefficients

/-!
# Compatibility with the native power-series foundation

Alex Dobner's concrete bounded symmetric series remain the native foundation.
The polynomial presentation is an equivalent interface for the downstream library.
No permutation action is installed globally, and the grading remains weighted.
-/

noncomputable section
namespace SymmetricFunction
variable (σ R : Type*) [CommRing R] [Infinite σ]

/-- The polynomial-backed interface and the native symmetric-function algebra agree
for every infinite alphabet, via the upstream fundamental theorem. -/
def upstreamEquiv : SymmetricFunction R ≃ₐ[R] MvPowerSeries.symmetricFunctionSubalgebra σ R :=
  (polynomialEquiv R).trans (MvPowerSeries.esymmAlgEquiv σ R)

@[simp] theorem upstreamEquiv_e (i : ℕ+) :
    upstreamEquiv σ R (e i) =
      (MvPowerSeries.esymmGraded σ R i : MvPowerSeries.symmetricFunctionSubalgebra σ R) := by
  simp [upstreamEquiv]

/-- The unit convention agrees at degree zero as well as at positive degrees. -/
@[simp] theorem coe_upstreamEquiv_e (n : ℕ) :
    (upstreamEquiv σ R (e n) : MvPowerSeries σ R) = MvPowerSeries.esymm σ R n := by
  cases n with
  | zero => simp
  | succ n => exact congrArg Subtype.val (upstreamEquiv_e σ R ⟨n + 1, Nat.succ_pos n⟩)

/-- The equivalence preserves exactly the original internal homogeneous pieces. -/
@[simp] theorem upstreamEquiv_mem_grading_iff (f : SymmetricFunction R) (n : ℕ) :
    upstreamEquiv σ R f ∈ MvPowerSeries.symmetricFunctionGrading σ R n ↔
      IsHomogeneous f n :=
  MvPowerSeries.esymmAlgEquiv_mem_grading_iff σ R n (polynomialEquiv R f)

/-- Homogeneous projections agree, not just membership in each homogeneous piece. -/
theorem upstreamEquiv_homogeneousComponent (f : SymmetricFunction R) (n : ℕ) :
    upstreamEquiv σ R (homogeneousComponent n f) =
      GradedAlgebra.proj (MvPowerSeries.symmetricFunctionGrading σ R) n (upstreamEquiv σ R f) := by
  change MvPowerSeries.esymmAlgHom σ R (polynomialEquiv R (homogeneousComponent n f)) = _
  rw [polynomialEquiv_homogeneousComponent]
  exact MvPowerSeries.esymmAlgHom_weightedHomogeneousComponent σ R n _

end SymmetricFunction

namespace MvPowerSeries
variable {R σ : Type*} [CommRing R] [Fintype σ]

/-- The native elementary series agrees with Mathlib's elementary polynomial
in every finite alphabet, including degree zero and too-small alphabets. -/
theorem coe_polynomial_esymm (n : ℕ) :
    (MvPolynomial.esymm σ R n : MvPowerSeries σ R) = esymm σ R n := by
  classical
  have hexp (s : Finset σ) (a : σ →₀ ℕ) :
      (∑ i ∈ s, Finsupp.single i 1) = a ↔
        s = a.support ∧ ∀ i ∈ a.support, a i = 1 := by
    have hs : (∑ i ∈ s, Finsupp.single i (1 : ℕ)).support = s := by
      ext i
      simp [Finsupp.mem_support_iff, Finsupp.finsetSum_apply, Finsupp.single_apply, eq_comm]
    constructor
    · intro h
      refine ⟨by rw [← h, hs], ?_⟩
      intro i hi
      rw [← h, hs] at hi
      rw [← h]
      simp [Finsupp.finsetSum_apply, Finsupp.single_apply, hi, eq_comm]
    · rintro ⟨rfl, ha⟩
      ext i
      by_cases hi : i ∈ a.support
      · simp [Finsupp.finsetSum_apply, Finsupp.single_apply, hi, ha i hi, eq_comm]
      · simp [Finsupp.finsetSum_apply, Finsupp.single_apply, hi,
          Finsupp.notMem_support_iff.mp hi, eq_comm]
  ext a
  rw [MvPolynomial.coeff_coe, MvPolynomial.esymm_eq_sum_monomial, MvPolynomial.coeff_sum,
    coeff_esymm]
  simp only [MvPolynomial.coeff_monomial, hexp]
  by_cases ha : ∀ i ∈ a.support, a i = 1
  · simp only [show (∀ i ∈ a.support, a i = 1) ↔ True from iff_true_intro ha, and_true, Finset.sum_ite_eq', Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
  · simp only [show (∀ i ∈ a.support, a i = 1) ↔ False from iff_false_intro ha, and_false, ite_false, Finset.sum_const_zero]

end MvPowerSeries

namespace SymmetricFunction
variable (R : Type*) [CommRing R]

/-- Both libraries realize elementary generators as the identical actual series. -/
theorem toSeries_e_eq_upstream (n : ℕ) :
    toSeries R (e n) = MvPowerSeries.esymm ℕ R n := by
  apply SymmetricFunctions.Series.eq_of_finiteRestriction_eq
  intro N
  rw [finiteRestriction_toSeries_e, MvPowerSeries.coe_polynomial_esymm]
  exact (MvPowerSeries.killCompl_esymm ℕ R Fin.valEmbedding n).symm

end SymmetricFunction

namespace SymmetricFunction
variable (R : Type*) [CommRing R]

/-- On the natural alphabet the abstract equivalence is the actual series realization. -/
@[simp] theorem coe_upstreamEquiv (f : SymmetricFunction R) :
    (upstreamEquiv ℕ R f : MvPowerSeries ℕ R) = toSeries R f := by
  have he : (MvPowerSeries.symmetricFunctionSubalgebra ℕ R).val.comp
      (upstreamEquiv ℕ R).toAlgHom = toSeries R := by
    apply algHom_ext
    intro i
    change (upstreamEquiv ℕ R (e i) : MvPowerSeries ℕ R) = toSeries R (e i)
    rw [coe_upstreamEquiv_e, toSeries_e_eq_upstream]
  exact AlgHom.congr_fun he f

/-- The coefficient-one complete functions of both implementations agree. -/
@[simp] theorem coe_upstreamEquiv_h (n : ℕ) :
    (upstreamEquiv ℕ R (h n) : MvPowerSeries ℕ R) = MvPowerSeries.hsymm ℕ R n := by
  rw [coe_upstreamEquiv]
  ext a
  obtain ⟨N, b, rfl⟩ := SymmetricFunctions.Series.exists_fin_exponent a
  rw [← SymmetricFunctions.Series.coeff_finiteRestriction, finiteRestriction_toSeries_h,
    MvPolynomial.coeff_coe]
  have hc : (MvPolynomial.hsymm (Fin N) R n).coeff b =
      if b.degree = n then 1 else 0 := by
    convert SymmetricFunctions.coeff_hsymm (R := R) b n using 1
    congr 2
    exact congrArg (fun dec : DecidableEq (Fin N) =>
      @MvPolynomial.hsymm (Fin N) R _ _ dec n) (Subsingleton.elim _ _)
  refine hc.trans ?_
  rw [MvPowerSeries.coeff_hsymm]
  have hd : (b.embDomain Fin.valEmbedding).degree = b.degree :=
    congrArg Multiset.sum (SymmetricFunctions.exponentParts_embDomain Fin.valEmbedding b)
  rw [hd]

@[simp] theorem upstreamEquiv_h (n : ℕ) :
    upstreamEquiv ℕ R (h n) =
      (MvPowerSeries.hsymmGraded ℕ R n : MvPowerSeries.symmetricFunctionSubalgebra ℕ R) :=
  Subtype.ext (coe_upstreamEquiv_h R n)

/-- Monomial functions agree as actual coefficient-one orbit sums. -/
@[simp] theorem coe_upstreamEquiv_mPart {d : ℕ} (μ : Nat.Partition d) :
    (upstreamEquiv ℕ R (mPart μ) : MvPowerSeries ℕ R) = MvPowerSeries.msymmPart ℕ R μ := by
  rw [coe_upstreamEquiv]
  ext a
  have hp : a.toAllPartitions = μ.toAllPartitions ↔
      SymmetricFunctions.exponentParts a = μ.parts :=
    ⟨fun h => congrArg AllPartitions.parts h, fun h => AllPartitions.ext h⟩
  simp only [coeff_toSeries_mPart, MvPowerSeries.coeff_msymmPart, hp]

/-- The two bounded subalgebras have the same underlying series and membership conditions. -/
theorem boundedSymmetricSubalgebra_eq_upstream :
    SymmetricFunctions.Series.boundedSymmetricSubalgebra R =
      MvPowerSeries.symmetricFunctionSubalgebra ℕ R := by
  ext f
  rw [MvPowerSeries.mem_symmetricFunctionSubalgebra]
  change (SymmetricFunctions.Series.IsSymmetric f ∧
    SymmetricFunctions.Series.HasBoundedTotalDegree f) ↔
    MvPowerSeries.HasBoundedDegree f ∧ MvPowerSeries.IsSymmetric f
  exact and_comm

end SymmetricFunction
