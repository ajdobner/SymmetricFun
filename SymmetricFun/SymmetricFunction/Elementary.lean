module

public import SymmetricFun.SymmetricFunction.Grading
public import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# Elementary symmetric functions

The degree-`n` elementary symmetric function has coefficient one on the squarefree
monomials supported on exactly `n` variables, and zero elsewhere.
For a partition `μ`, `esymmPart` is the product of the elementary symmetric
functions indexed by its parts. The corresponding bundled elements are
`esymmGraded` and `esymmPartGraded`.
-/

@[expose] public section
noncomputable section

namespace MvPowerSeries

variable (σ R : Type*) [CommSemiring R]

/-- The degree-`n` elementary symmetric function as a power series. -/
def esymm (n : ℕ) : MvPowerSeries σ R :=
  fun c ↦ if c.support.card = n ∧ (∀ i ∈ c.support, c i = 1) then 1 else 0

@[simp]
theorem coeff_esymm (n : ℕ) (d : σ →₀ ℕ) :
    coeff d (esymm σ R n) =
      if d.support.card = n ∧ (∀ i ∈ d.support, d i = 1) then 1 else 0 := rfl

/-- An alternative coefficient formula using total degree and bounds on all exponents. -/
theorem coeff_esymm_eq_ite (n : ℕ) (d : σ →₀ ℕ) [Decidable (∀ i, d i ≤ 1)] :
    coeff d (esymm σ R n) =
      if d.degree = n ∧ (∀ i, d i ≤ 1) then 1 else 0 := by
  classical
  have hsquare : (∀ i ∈ d.support, d i = 1) ↔ ∀ i, d i ≤ 1 := by
    constructor
    · intro h i
      by_cases hi : i ∈ d.support
      · exact (h i hi).le
      · simp [Finsupp.notMem_support_iff.mp hi]
    · intro h i hi
      exact Nat.le_antisymm (h i) (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))
  rw [coeff_esymm]
  simp only [hsquare]
  by_cases h : ∀ i, d i ≤ 1
  · have hd : d.degree = d.support.card := by
      simp only [Finsupp.degree_apply, Finset.sum_congr rfl (hsquare.mpr h), Finset.sum_const,
        smul_eq_mul, mul_one]
    rw [hd]
  · simp only [h, and_false, ite_false]

/-- Restricting to a set of variables preserves elementary symmetric functions. -/
@[simp]
theorem killCompl_esymm {τ : Type*} (e : τ ↪ σ) (n : ℕ) :
    killCompl e (esymm σ R n) = esymm τ R n := by
  classical
  ext d
  simp [coeff_killCompl, coeff_esymm, Finsupp.support_embDomain]

@[simp]
theorem esymm_zero : esymm σ R 0 = 1 := by
  classical
  ext d
  by_cases h : d = 0 <;> simp [coeff_one, h]

theorem isHomogeneous_esymm (n : ℕ) : IsHomogeneous (esymm σ R n) n := by
  intro d hd
  change (if d.support.card = n ∧ (∀ i ∈ d.support, d i = 1) then 1 else 0 : R) ≠ 0 at hd
  split_ifs at hd with h
  · change Finsupp.weight (fun _ : σ => 1) d = n
    rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_apply,
      Finset.sum_congr rfl h.2]
    simpa using h.1
  · exact (hd rfl).elim

theorem isSymmetric_esymm (n : ℕ) : IsSymmetric (esymm σ R n) := by
  classical
  intro e
  ext d
  simp [renameEquiv_coeff, Finsupp.equivMapDomain,
    e.forall_congr_right (q := fun i => d i ≠ 0 → d i = 1)]

theorem esymm_mem_symmetricFunctionSubalgebra (n : ℕ) :
    esymm σ R n ∈ symmetricFunctionSubalgebra σ R :=
  mem_symmetricFunctionSubalgebra_of_isHomogeneous
    (isHomogeneous_esymm σ R n) (isSymmetric_esymm σ R n)

/-- The elementary symmetric function bundled in its graded piece. -/
def esymmGraded (n : ℕ) : symmetricFunctionGrading σ R n :=
  symmetricFunctionGrading.mk (esymm σ R n)
    (isHomogeneous_esymm σ R n) (isSymmetric_esymm σ R n)

@[simp]
theorem coe_esymmGraded (n : ℕ) :
    (esymmGraded σ R n : MvPowerSeries σ R) = esymm σ R n := rfl

/-- The product of elementary symmetric functions indexed by the parts of `μ`. -/
def esymmPart {n : ℕ} (μ : Nat.Partition n) : MvPowerSeries σ R :=
  (μ.parts.map (esymm σ R)).prod

/-- Any finite enumeration of the parts can be used to form the elementary product. -/
theorem esymmPart_eq_prod {n : ℕ} (μ : Nat.Partition n) {I : Type*} [Fintype I]
    (a : I → ℕ) (ha : Finset.univ.val.map a = μ.parts) :
    esymmPart σ R μ = ∏ i, esymm σ R (a i) := by
  rw [esymmPart, ← ha, Multiset.map_map]
  rfl

@[simp]
theorem esymmPart_indiscrete (n : ℕ) :
    esymmPart σ R (Nat.Partition.indiscrete n) = esymm σ R n := by
  cases n <;> simp [esymmPart]

@[simp]
theorem esymmPart_zero (μ : Nat.Partition 0) : esymmPart σ R μ = 1 := by
  simp [esymmPart]

theorem isHomogeneous_esymmPart {n : ℕ} (μ : Nat.Partition n) :
    IsHomogeneous (esymmPart σ R μ) n := by
  intro d hd
  have h :=
    IsHomogeneous.multiset_prod μ.parts (esymm σ R) id
      (fun i _ => isHomogeneous_esymm σ R i) hd
  simpa only [Multiset.map_id, μ.parts_sum] using h

theorem isSymmetric_esymmPart {n : ℕ} (μ : Nat.Partition n) :
    IsSymmetric (esymmPart σ R μ) :=
  IsSymmetric.multiset_prod μ.parts (esymm σ R) (fun i _ => isSymmetric_esymm σ R i)

theorem esymmPart_mem_symmetricFunctionSubalgebra {n : ℕ} (μ : Nat.Partition n) :
    esymmPart σ R μ ∈ symmetricFunctionSubalgebra σ R :=
  mem_symmetricFunctionSubalgebra_of_isHomogeneous
    (isHomogeneous_esymmPart σ R μ) (isSymmetric_esymmPart σ R μ)

/-- An elementary symmetric product bundled in the degree-`n` piece. -/
def esymmPartGraded {n : ℕ} (μ : Nat.Partition n) : symmetricFunctionGrading σ R n :=
  symmetricFunctionGrading.mk (esymmPart σ R μ)
    (isHomogeneous_esymmPart σ R μ) (isSymmetric_esymmPart σ R μ)

@[simp]
theorem coe_esymmPartGraded {n : ℕ} (μ : Nat.Partition n) :
    (esymmPartGraded σ R μ : MvPowerSeries σ R) = esymmPart σ R μ := rfl

@[simp]
theorem esymmPartGraded_indiscrete (n : ℕ) :
    esymmPartGraded σ R (Nat.Partition.indiscrete n) = esymmGraded σ R n := by
  apply symmetricFunctionGrading.ext
  simp

end MvPowerSeries
