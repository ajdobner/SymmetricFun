module

public import SymmetricFun.SymmetricFunction.Grading
public import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# Complete homogeneous symmetric functions

The degree-`n` complete homogeneous symmetric function has coefficient one on
every monomial of total degree `n`, and zero elsewhere.
For a partition `μ`, `hsymmPart` is the product of complete homogeneous
symmetric functions indexed by its parts. Their bundled versions are
`hsymmGraded` and `hsymmPartGraded`.
-/

@[expose] public section
noncomputable section

namespace MvPowerSeries

variable (σ R : Type*) [CommSemiring R]

/-- The degree-`n` complete homogeneous symmetric function as a power series. -/
def hsymm (n : ℕ) : MvPowerSeries σ R :=
  fun c ↦ if c.degree = n then 1 else 0

@[simp]
theorem coeff_hsymm (n : ℕ) (d : σ →₀ ℕ) :
    coeff d (hsymm σ R n) = if d.degree = n then 1 else 0 := rfl

@[simp]
theorem hsymm_zero : hsymm σ R 0 = 1 := by
  classical
  ext d
  simp [coeff_one, Finsupp.degree_eq_zero_iff]

theorem isHomogeneous_hsymm (n : ℕ) : IsHomogeneous (hsymm σ R n) n := by
  intro d hd
  change (if d.degree = n then 1 else 0 : R) ≠ 0 at hd
  split_ifs at hd with h
  · change Finsupp.weight (fun _ : σ => 1) d = n
    rwa [← Finsupp.degree_eq_weight_one]
  · exact (hd rfl).elim

theorem isSymmetric_hsymm (n : ℕ) : IsSymmetric (hsymm σ R n) := by
  intro e
  ext d
  simp [renameEquiv_coeff, Finsupp.equivMapDomain_eq_mapDomain, Finsupp.degree_mapDomain]

theorem hsymm_mem_symmetricFunctionSubalgebra (n : ℕ) :
    hsymm σ R n ∈ symmetricFunctionSubalgebra σ R :=
  mem_symmetricFunctionSubalgebra_of_isHomogeneous
    (isHomogeneous_hsymm σ R n) (isSymmetric_hsymm σ R n)

/-- The complete homogeneous symmetric function bundled in its graded piece. -/
def hsymmGraded (n : ℕ) : symmetricFunctionGrading σ R n :=
  symmetricFunctionGrading.mk (hsymm σ R n)
    (isHomogeneous_hsymm σ R n) (isSymmetric_hsymm σ R n)

@[simp]
theorem coe_hsymmGraded (n : ℕ) :
    (hsymmGraded σ R n : MvPowerSeries σ R) = hsymm σ R n := rfl

/-- The product of complete homogeneous symmetric functions indexed by the parts of `μ`. -/
def hsymmPart {n : ℕ} (μ : Nat.Partition n) : MvPowerSeries σ R :=
  (μ.parts.map (hsymm σ R)).prod

@[simp]
theorem hsymmPart_indiscrete (n : ℕ) :
    hsymmPart σ R (Nat.Partition.indiscrete n) = hsymm σ R n := by
  cases n <;> simp [hsymmPart]

@[simp]
theorem hsymmPart_zero (μ : Nat.Partition 0) : hsymmPart σ R μ = 1 := by
  simp [hsymmPart]

theorem isHomogeneous_hsymmPart {n : ℕ} (μ : Nat.Partition n) :
    IsHomogeneous (hsymmPart σ R μ) n := by
  intro d hd
  have h :=
    IsHomogeneous.multiset_prod μ.parts (hsymm σ R) id
      (fun i _ => isHomogeneous_hsymm σ R i) hd
  simpa only [Multiset.map_id, μ.parts_sum] using h

theorem isSymmetric_hsymmPart {n : ℕ} (μ : Nat.Partition n) :
    IsSymmetric (hsymmPart σ R μ) :=
  IsSymmetric.multiset_prod μ.parts (hsymm σ R) (fun i _ => isSymmetric_hsymm σ R i)

theorem hsymmPart_mem_symmetricFunctionSubalgebra {n : ℕ} (μ : Nat.Partition n) :
    hsymmPart σ R μ ∈ symmetricFunctionSubalgebra σ R :=
  mem_symmetricFunctionSubalgebra_of_isHomogeneous
    (isHomogeneous_hsymmPart σ R μ) (isSymmetric_hsymmPart σ R μ)

/-- A complete homogeneous symmetric product bundled in the degree-`n` piece. -/
def hsymmPartGraded {n : ℕ} (μ : Nat.Partition n) : symmetricFunctionGrading σ R n :=
  symmetricFunctionGrading.mk (hsymmPart σ R μ)
    (isHomogeneous_hsymmPart σ R μ) (isSymmetric_hsymmPart σ R μ)

@[simp]
theorem coe_hsymmPartGraded {n : ℕ} (μ : Nat.Partition n) :
    (hsymmPartGraded σ R μ : MvPowerSeries σ R) = hsymmPart σ R μ := rfl

@[simp]
theorem hsymmPartGraded_indiscrete (n : ℕ) :
    hsymmPartGraded σ R (Nat.Partition.indiscrete n) = hsymmGraded σ R n := by
  apply symmetricFunctionGrading.ext
  simp

end MvPowerSeries
