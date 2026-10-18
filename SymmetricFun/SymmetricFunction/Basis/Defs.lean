module

public import SymmetricFun.Partition.Finsupp
public import SymmetricFun.Partition.Multiplicity
public import SymmetricFun.SymmetricFunction.Grading
public import SymmetricFun.Tableau.Kostka
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Families of symmetric functions

This file defines the monomial, elementary, complete homogeneous, and Schur symmetric
functions and their basic coefficient, symmetry, and homogeneity properties.

* `msymmPart σ R μ` has coefficient one on exponent vectors whose partition is `μ`.
* `esymm σ R n` has coefficient one on squarefree monomials of degree `n`.
* `hsymm σ R n` has coefficient one on all monomials of degree `n`.
* `skewSsymmPart σ R π μ` has skew Kostka coefficients for the shape `π / μ`.
* `ssymmPart σ R π` specializes to the empty inner shape.

The elementary and complete partition products are `esymmPart` and `hsymmPart`.
Each family also has a version bundled in `symmetricFunctionGrading`, with a name
ending in `Graded`. For an index `μ : IntegerPartition`, use its partition `μ.2`.
For skew Schur functions with outer size `n` and inner size `m`, the degree-`d`
homogeneity theorem and graded version take a hypothesis `hd : n = m + d`.

The polynomial evaluation maps `esymmAlgHom` and `hsymmAlgHom` send the variable
indexed by a positive integer `i` to the corresponding degree-`i` function.
Their graded versions are `esymmGradedAlgHom` and `hsymmGradedAlgHom`, with weight
`i` assigned to that variable. The evaluation formulas and grading compatibility
hold over a commutative semiring for any variable type.

Coordinates, basis constructions, and transition formulas are developed in the
other modules of `SymmetricFunction/Basis`.
-/

@[expose] public section
noncomputable section

namespace MvPowerSeries

/-! ## Monomial symmetric functions -/

section MonomialSymmetric
variable (σ R : Type*) [CommSemiring R] {n : ℕ} (μ : Nat.Partition n)

/-- The monomial symmetric power series indexed by a partition of `n`. -/
def msymmPart : MvPowerSeries σ R :=
  fun (m : σ →₀ ℕ) =>
    if m.toIntegerPartition = μ.toIntegerPartition then 1 else 0

theorem isHomogeneous_msymmPart : IsHomogeneous (msymmPart σ R μ) n := by
  intro m hm
  change (if m.toIntegerPartition = μ.toIntegerPartition then 1 else 0 : R) ≠ 0 at hm
  split_ifs at hm with h
  · rw [← m.toIntegerPartition_size, h, Nat.Partition.size_toIntegerPartition]
  · exact (hm rfl).elim

@[simp]
lemma coeff_msymmPart {σ R : Type*} [CommSemiring R]
    (μ : Nat.Partition n) (m : σ →₀ ℕ) :
    coeff m (msymmPart σ R μ) = if m.toIntegerPartition = μ.toIntegerPartition then 1 else 0 := rfl

theorem isSymmetric_msymmPart : IsSymmetric (msymmPart σ R μ) := by
  intro e
  ext m
  simp only [renameEquiv_coeff, coeff_msymmPart, Finsupp.toIntegerPartition_equivMapDomain]

lemma msymmPart_mem_symmetricFunctionSubalgebra :
    msymmPart σ R μ ∈ symmetricFunctionSubalgebra σ R :=
  mem_symmetricFunctionSubalgebra_of_isHomogeneous
    (isHomogeneous_msymmPart σ R μ) (isSymmetric_msymmPart σ R μ)

/-- A monomial symmetric function as an element of the degree-`n` piece of the
symmetric-function algebra. -/
def msymmPartGraded : symmetricFunctionGrading σ R n :=
  symmetricFunctionGrading.mk (msymmPart σ R μ)
    (isHomogeneous_msymmPart σ R μ) (isSymmetric_msymmPart σ R μ)

@[simp]
theorem coe_msymmPartGraded :
    (msymmPartGraded σ R μ : MvPowerSeries σ R) = msymmPart σ R μ :=
  rfl

end MonomialSymmetric

/-! ## Elementary symmetric functions -/

section ElementarySymmetric

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

@[simp]
theorem coe_esymmGraded_zero :
    (esymmGraded σ R 0 : symmetricFunctionSubalgebra σ R) = 1 :=
  Subtype.ext (esymm_zero σ R)

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

end ElementarySymmetric

/-! ## Complete homogeneous symmetric functions -/

section CompleteHomogeneousSymmetric

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

@[simp]
theorem coe_hsymmGraded_zero :
    (hsymmGraded σ R 0 : symmetricFunctionSubalgebra σ R) = 1 :=
  Subtype.ext (hsymm_zero σ R)

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

end CompleteHomogeneousSymmetric

/-! ## Schur functions -/

section Schur

variable (σ R : Type*) [CommSemiring R]

/-- The skew Schur power series of shape `π / μ`, defined by its Kostka coefficients. -/
def skewSsymmPart {n m : ℕ} (π : Nat.Partition n) (μ : Nat.Partition m) :
    MvPowerSeries σ R :=
  fun a => (Nat.Partition.skewKostka π μ a.toIntegerPartition.2 : R)

@[simp]
theorem coeff_skewSsymmPart {n m : ℕ} (π : Nat.Partition n) (μ : Nat.Partition m)
    (a : σ →₀ ℕ) :
    coeff a (skewSsymmPart σ R π μ) =
      (Nat.Partition.skewKostka π μ a.toIntegerPartition.2 : R) := rfl

/-- The ordinary Schur power series is the skew Schur series with empty inner shape. -/
def ssymmPart {n : ℕ} (π : Nat.Partition n) : MvPowerSeries σ R :=
  skewSsymmPart σ R π (default : Nat.Partition 0)

@[simp]
theorem skewSsymmPart_empty_inner {n : ℕ} (π : Nat.Partition n) :
    skewSsymmPart σ R π (default : Nat.Partition 0) = ssymmPart σ R π := rfl

@[simp]
theorem coeff_ssymmPart {n : ℕ} (π : Nat.Partition n) (a : σ →₀ ℕ) :
    coeff a (ssymmPart σ R π) = (Nat.Partition.kostka π a.toIntegerPartition.2 : R) := rfl

theorem isSymmetric_skewSsymmPart {n m : ℕ} (π : Nat.Partition n) (μ : Nat.Partition m) :
    IsSymmetric (skewSsymmPart σ R π μ) := by
  intro e
  ext a
  rw [renameEquiv_coeff, coeff_skewSsymmPart, coeff_skewSsymmPart,
    Finsupp.toIntegerPartition_equivMapDomain]

theorem isSymmetric_ssymmPart {n : ℕ} (π : Nat.Partition n) :
    IsSymmetric (ssymmPart σ R π) :=
  isSymmetric_skewSsymmPart σ R π default

private theorem size_eq_of_coeff_skewSsymmPart_ne_zero {n m : ℕ}
    (π : Nat.Partition n) (μ : Nat.Partition m) {a : σ →₀ ℕ}
    (ha : coeff a (skewSsymmPart σ R π μ) ≠ 0) : n = m + a.degree := by
  by_contra h
  have hsize : m + a.toIntegerPartition.size ≠ n := by
    change m + a.degree ≠ n
    exact Ne.symm h
  apply ha
  rw [coeff_skewSsymmPart,
    Nat.Partition.skewKostka_eq_zero_of_size_ne π μ a.toIntegerPartition.2 hsize, Nat.cast_zero]

/-- A skew Schur series has degree `d` when the outer size is the inner size plus `d`. -/
theorem isHomogeneous_skewSsymmPart {n m d : ℕ}
    (π : Nat.Partition n) (μ : Nat.Partition m) (hd : n = m + d) :
    IsHomogeneous (skewSsymmPart σ R π μ) d := by
  intro a ha
  have h := size_eq_of_coeff_skewSsymmPart_ne_zero σ R π μ ha
  change Finsupp.weight (fun _ : σ => 1) a = d
  rw [← Finsupp.degree_eq_weight_one]
  omega

theorem isHomogeneous_ssymmPart {n : ℕ} (π : Nat.Partition n) :
    IsHomogeneous (ssymmPart σ R π) n :=
  isHomogeneous_skewSsymmPart σ R π default (by simp)

theorem skewSsymmPart_mem_symmetricFunctionSubalgebra {n m : ℕ}
    (π : Nat.Partition n) (μ : Nat.Partition m) :
    skewSsymmPart σ R π μ ∈ symmetricFunctionSubalgebra σ R := by
  rw [mem_symmetricFunctionSubalgebra]
  refine ⟨⟨n, fun a ha => ?_⟩, isSymmetric_skewSsymmPart σ R π μ⟩
  have h := size_eq_of_coeff_skewSsymmPart_ne_zero σ R π μ ha
  omega

theorem ssymmPart_mem_symmetricFunctionSubalgebra {n : ℕ} (π : Nat.Partition n) :
    ssymmPart σ R π ∈ symmetricFunctionSubalgebra σ R :=
  skewSsymmPart_mem_symmetricFunctionSubalgebra σ R π default

/-- A skew Schur function bundled in its specified degree. -/
def skewSsymmPartGraded {n m d : ℕ}
    (π : Nat.Partition n) (μ : Nat.Partition m) (hd : n = m + d) :
    symmetricFunctionGrading σ R d :=
  symmetricFunctionGrading.mk (skewSsymmPart σ R π μ)
    (isHomogeneous_skewSsymmPart σ R π μ hd) (isSymmetric_skewSsymmPart σ R π μ)

@[simp]
theorem coe_skewSsymmPartGraded {n m d : ℕ}
    (π : Nat.Partition n) (μ : Nat.Partition m) (hd : n = m + d) :
    (skewSsymmPartGraded σ R π μ hd : MvPowerSeries σ R) = skewSsymmPart σ R π μ := rfl

/-- A Schur function bundled in the degree of its shape. -/
def ssymmPartGraded {n : ℕ} (π : Nat.Partition n) : symmetricFunctionGrading σ R n :=
  symmetricFunctionGrading.mk (ssymmPart σ R π)
    (isHomogeneous_ssymmPart σ R π) (isSymmetric_ssymmPart σ R π)

@[simp]
theorem coe_ssymmPartGraded {n : ℕ} (π : Nat.Partition n) :
    (ssymmPartGraded σ R π : MvPowerSeries σ R) = ssymmPart σ R π := rfl

/-- In `k` variables, a skew Schur coefficient counts tableaux of the given weight. -/
theorem coeff_skewSsymmPart_eq_skewKostkaWeight {k n m : ℕ}
    (π : Nat.Partition n) (μ : Nat.Partition m) (a : Fin k →₀ ℕ) :
    coeff a (skewSsymmPart (Fin k) R π μ) =
      (Nat.Partition.skewKostkaWeight π μ (fun i => a i) : R) := by
  rw [coeff_skewSsymmPart, ← Finsupp.ofFn_eq_toIntegerPartition a,
    ← Nat.Partition.skewKostkaWeight_eq_skewKostka]

/-- The ordinary Schur coefficient formula is the empty-inner-shape case. -/
theorem coeff_ssymmPart_eq_skewKostkaWeight {k n : ℕ}
    (π : Nat.Partition n) (a : Fin k →₀ ℕ) :
    coeff a (ssymmPart (Fin k) R π) =
      (Nat.Partition.skewKostkaWeight π (default : Nat.Partition 0) (fun i => a i) : R) :=
  coeff_skewSsymmPart_eq_skewKostkaWeight R π default a

end Schur

/-! ## Polynomial evaluation -/

section PolynomialEvaluation

variable (σ R : Type*) [CommSemiring R]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-! ### Elementary evaluation -/

/-- Evaluate a polynomial in the elementary symmetric functions of positive degree. -/
def esymmAlgHom :
    MvPolynomial ℕ+ R →ₐ[R] symmetricFunctionSubalgebra σ R :=
  MvPolynomial.aeval (fun i : ℕ+ =>
    (esymmGraded σ R (i : ℕ) : symmetricFunctionSubalgebra σ R))

@[simp]
theorem esymmAlgHom_X (i : ℕ+) :
    esymmAlgHom σ R (MvPolynomial.X i) =
      (esymmGraded σ R (i : ℕ) : symmetricFunctionSubalgebra σ R) := by
  simp [esymmAlgHom]

/-- A polynomial monomial evaluates to the elementary product with those part multiplicities. -/
theorem esymmAlgHom_monomial (a : ℕ+ →₀ ℕ) (r : R) :
    esymmAlgHom σ R (MvPolynomial.monomial a r) =
      r • (esymmPartGraded σ R (IntegerPartition.ofMultiplicities a).2 :
        symmetricFunctionSubalgebra σ R) := by
  have hprod :
      (((IntegerPartition.ofMultiplicities a).parts).map (esymm σ R)).prod =
        a.prod (fun i k => esymm σ R (i : ℕ) ^ k) := by
    rw [IntegerPartition.parts_ofMultiplicities, Multiset.map_map, Finsupp.toMultiset_map,
      Finsupp.prod_toMultiset,
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    rfl
  rw [esymmAlgHom, MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  apply congrArg (r • ·)
  apply Subtype.ext
  change (symmetricFunctionSubalgebra σ R).val
      (a.prod (fun i k => (esymmGraded σ R (i : ℕ) :
        symmetricFunctionSubalgebra σ R) ^ k)) =
    esymmPart σ R (IntegerPartition.ofMultiplicities a).2
  rw [map_finsuppProd]
  simp only [map_pow]
  exact hprod.symm

/-- Evaluation sends weighted homogeneous polynomials to the corresponding symmetric piece. -/
theorem esymmAlgHom_mem_grading {n : ℕ} {p : MvPolynomial ℕ+ R}
    (hp : p ∈ MvPolynomial.weightedHomogeneousSubmodule R PNat.val n) :
    esymmAlgHom σ R p ∈ symmetricFunctionGrading σ R n := by
  change p.IsWeightedHomogeneous PNat.val n at hp
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
    rw [map_zero]
    exact (symmetricFunctionGrading σ R n).zero_mem
  | add p q hp hq ihp ihq =>
    rw [map_add]
    exact (symmetricFunctionGrading σ R n).add_mem ihp ihq
  | monomial a r ha =>
    rw [esymmAlgHom_monomial]
    apply (symmetricFunctionGrading σ R n).smul_mem
    rw [← ha, ← IntegerPartition.size_ofMultiplicities]
    exact (esymmPartGraded σ R (IntegerPartition.ofMultiplicities a).2).property

/-- Evaluation in elementary symmetric functions as a graded algebra homomorphism,
where the polynomial variable indexed by `i` has weight `i`. -/
def esymmGradedAlgHom :
    MvPolynomial.weightedHomogeneousSubmodule R PNat.val →ₐᵍ[R]
      symmetricFunctionGrading σ R :=
  { esymmAlgHom σ R with map_mem := esymmAlgHom_mem_grading σ R }

@[simp]
theorem esymmGradedAlgHom_toAlgHom :
    (esymmGradedAlgHom σ R).toAlgHom = esymmAlgHom σ R := rfl

@[simp]
theorem esymmGradedAlgHom_apply (p : MvPolynomial ℕ+ R) :
    esymmGradedAlgHom σ R p = esymmAlgHom σ R p := rfl

/-- Evaluation commutes with projection onto each weighted homogeneous component. -/
theorem esymmAlgHom_weightedHomogeneousComponent (n : ℕ) (p : MvPolynomial ℕ+ R) :
    esymmAlgHom σ R (MvPolynomial.weightedHomogeneousComponent PNat.val n p) =
      GradedAlgebra.proj (symmetricFunctionGrading σ R) n (esymmAlgHom σ R p) := by
  have h := map_directSumDecompose (MvPolynomial.weightedHomogeneousSubmodule R PNat.val)
    (symmetricFunctionGrading σ R) (esymmGradedAlgHom σ R) (x := p) (i := n)
  change esymmAlgHom σ R (MvPolynomial.decompose' R PNat.val p n : MvPolynomial ℕ+ R) = _ at h
  rw [MvPolynomial.decompose'_apply] at h
  exact h

/-! ### Complete homogeneous evaluation -/

/-- Evaluate a polynomial in the complete homogeneous symmetric functions of positive degree. -/
def hsymmAlgHom :
    MvPolynomial ℕ+ R →ₐ[R] symmetricFunctionSubalgebra σ R :=
  MvPolynomial.aeval (fun i : ℕ+ =>
    (hsymmGraded σ R (i : ℕ) : symmetricFunctionSubalgebra σ R))

@[simp]
theorem hsymmAlgHom_X (i : ℕ+) :
    hsymmAlgHom σ R (MvPolynomial.X i) =
      (hsymmGraded σ R (i : ℕ) : symmetricFunctionSubalgebra σ R) := by
  simp [hsymmAlgHom]

/-- A monomial evaluates to the complete homogeneous product with those part multiplicities. -/
theorem hsymmAlgHom_monomial (a : ℕ+ →₀ ℕ) (r : R) :
    hsymmAlgHom σ R (MvPolynomial.monomial a r) =
      r • (hsymmPartGraded σ R (IntegerPartition.ofMultiplicities a).2 :
        symmetricFunctionSubalgebra σ R) := by
  have hprod :
      (((IntegerPartition.ofMultiplicities a).parts).map (hsymm σ R)).prod =
        a.prod (fun i k => hsymm σ R (i : ℕ) ^ k) := by
    rw [IntegerPartition.parts_ofMultiplicities, Multiset.map_map, Finsupp.toMultiset_map,
      Finsupp.prod_toMultiset,
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    rfl
  rw [hsymmAlgHom, MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  apply congrArg (r • ·)
  apply Subtype.ext
  change (symmetricFunctionSubalgebra σ R).val
      (a.prod (fun i k => (hsymmGraded σ R (i : ℕ) :
        symmetricFunctionSubalgebra σ R) ^ k)) =
    hsymmPart σ R (IntegerPartition.ofMultiplicities a).2
  rw [map_finsuppProd]
  simp only [map_pow]
  exact hprod.symm

/-- Complete homogeneous evaluation preserves the weighted grading. -/
theorem hsymmAlgHom_mem_grading {n : ℕ} {p : MvPolynomial ℕ+ R}
    (hp : p ∈ MvPolynomial.weightedHomogeneousSubmodule R PNat.val n) :
    hsymmAlgHom σ R p ∈ symmetricFunctionGrading σ R n := by
  change p.IsWeightedHomogeneous PNat.val n at hp
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
    rw [map_zero]
    exact (symmetricFunctionGrading σ R n).zero_mem
  | add p q hp hq ihp ihq =>
    rw [map_add]
    exact (symmetricFunctionGrading σ R n).add_mem ihp ihq
  | monomial a r ha =>
    rw [hsymmAlgHom_monomial]
    apply (symmetricFunctionGrading σ R n).smul_mem
    rw [← ha, ← IntegerPartition.size_ofMultiplicities]
    exact (hsymmPartGraded σ R (IntegerPartition.ofMultiplicities a).2).property

/-- Complete homogeneous evaluation as a graded algebra homomorphism. -/
def hsymmGradedAlgHom :
    MvPolynomial.weightedHomogeneousSubmodule R PNat.val →ₐᵍ[R]
      symmetricFunctionGrading σ R :=
  { hsymmAlgHom σ R with map_mem := hsymmAlgHom_mem_grading σ R }

@[simp]
theorem hsymmGradedAlgHom_toAlgHom :
    (hsymmGradedAlgHom σ R).toAlgHom = hsymmAlgHom σ R := rfl

@[simp]
theorem hsymmGradedAlgHom_apply (p : MvPolynomial ℕ+ R) :
    hsymmGradedAlgHom σ R p = hsymmAlgHom σ R p := rfl

end PolynomialEvaluation

end MvPowerSeries
