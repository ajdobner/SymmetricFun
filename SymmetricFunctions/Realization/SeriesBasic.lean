import SymmetricFunctions.Basis.Monomial
import Mathlib.RingTheory.MvPowerSeries.Rename

/-! # Symmetric series and coefficient shapes

The permutation-invariant and uniformly bounded targets follow the design in
ajdobner/SymmetricFun, SymmetricPoly/MvPowerSeries/{Symmetric,Homogeneous,Bases}.lean,
commit 98938de95a12b3ed363653cb980588e2a9188cb8. The proofs are reconstructed
from pinned Mathlib and the accepted exponent-orbit API; no draft is imported.
-/

noncomputable section

namespace SymmetricFunctions.Series

variable {σ R : Type*} [CommRing R]

/-- Invariance under every permutation of the actual alphabet variables. -/
def IsSymmetric (f : MvPowerSeries σ R) : Prop :=
  ∀ e : Equiv.Perm σ, MvPowerSeries.rename e f = f

/-- The algebra of all symmetric series, with no degree bound. -/
def symmetricSubalgebra (σ R : Type*) [CommRing R] : Subalgebra R (MvPowerSeries σ R) where
  carrier := {f | IsSymmetric f}
  mul_mem' hf hg e := by simp [map_mul, hf e, hg e]
  add_mem' hf hg e := by simp [map_add, hf e, hg e]
  algebraMap_mem' r e := (MvPowerSeries.rename e).commutes r

@[simp] theorem mem_symmetricSubalgebra (f : MvPowerSeries σ R) :
    f ∈ symmetricSubalgebra σ R ↔ IsSymmetric f := Iff.rfl

/-- Symmetric coefficients depend only on the multiset of nonzero exponent values. -/
theorem IsSymmetric.coeff_eq {f : MvPowerSeries σ R} (hf : IsSymmetric f)
    {a b : σ →₀ ℕ} (hab : exponentParts a = exponentParts b) :
    MvPowerSeries.coeff a f = MvPowerSeries.coeff b f := by
  obtain ⟨e, he⟩ := exists_mapDomain_eq_of_exponentParts_eq hab
  have hc := MvPowerSeries.coeff_embDomain_rename e.toEmbedding f a
  rw [Finsupp.embDomain_eq_mapDomain] at hc
  change MvPowerSeries.coeff (a.mapDomain e) (MvPowerSeries.rename e f) =
    MvPowerSeries.coeff a f at hc
  rw [he, hf e] at hc
  exact hc.symm

/-- The coefficient-shape criterion is also sufficient for permutation invariance. -/
theorem isSymmetric_of_coeff_eq (f : MvPowerSeries σ R)
    (hf : ∀ a b, exponentParts a = exponentParts b →
      MvPowerSeries.coeff a f = MvPowerSeries.coeff b f) : IsSymmetric f := by
  intro e
  apply MvPowerSeries.ext
  intro b
  let a := b.embDomain e.symm.toEmbedding
  have ha : a.embDomain e.toEmbedding = b := by
    simp [a, Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp]
  rw [← ha]
  change MvPowerSeries.coeff (a.embDomain e.toEmbedding)
    (MvPowerSeries.rename e.toEmbedding f) = _
  rw [MvPowerSeries.coeff_embDomain_rename]
  exact hf _ _ (by simp)

/-- The series of a monomial orbit: each exponent vector has coefficient one once. -/
def monomialSeries {d : ℕ} (μ : Nat.Partition d) : MvPowerSeries σ R :=
  fun a => if exponentParts a = μ.parts then 1 else 0

@[simp] theorem coeff_monomialSeries {d : ℕ} (μ : Nat.Partition d) (a : σ →₀ ℕ) :
    MvPowerSeries.coeff a (monomialSeries (R := R) μ) =
      if exponentParts a = μ.parts then 1 else 0 := rfl

theorem isSymmetric_monomialSeries {d : ℕ} (μ : Nat.Partition d) :
    IsSymmetric (monomialSeries (σ := σ) (R := R) μ) :=
  isSymmetric_of_coeff_eq _ fun a b hab => by simp [hab]

/-- One uniform total-degree bound on all nonzero coefficients. -/
def HasBoundedTotalDegree (f : MvPowerSeries σ R) : Prop :=
  ∃ D : ℕ, ∀ a, MvPowerSeries.coeff a f ≠ 0 → a.degree ≤ D

theorem HasBoundedTotalDegree.add {f g : MvPowerSeries σ R}
    (hf : HasBoundedTotalDegree f) (hg : HasBoundedTotalDegree g) :
    HasBoundedTotalDegree (f + g) := by
  obtain ⟨m, hm⟩ := hf
  obtain ⟨n, hn⟩ := hg
  refine ⟨max m n, fun a ha => ?_⟩
  by_cases h : MvPowerSeries.coeff a f = 0
  · exact (hn a (by simpa [h] using ha)).trans (le_max_right _ _)
  · exact (hm a h).trans (le_max_left _ _)

theorem HasBoundedTotalDegree.mul {f g : MvPowerSeries σ R}
    (hf : HasBoundedTotalDegree f) (hg : HasBoundedTotalDegree g) :
    HasBoundedTotalDegree (f * g) := by
  classical
  obtain ⟨m, hm⟩ := hf
  obtain ⟨n, hn⟩ := hg
  refine ⟨m + n, fun a ha => ?_⟩
  rw [MvPowerSeries.coeff_mul] at ha
  obtain ⟨⟨b, c⟩, hbc, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  rw [← Finset.mem_antidiagonal.mp hbc, map_add]
  exact add_le_add (hm b (left_ne_zero_of_mul hc)) (hn c (right_ne_zero_of_mul hc))

theorem hasBoundedTotalDegree_C (r : R) :
    HasBoundedTotalDegree (MvPowerSeries.C r : MvPowerSeries σ R) := by
  refine ⟨0, fun a ha => ?_⟩
  by_cases h : a = 0
  · simp [h]
  · exact False.elim (ha (MvPowerSeries.coeff_C_of_ne_zero h r))

/-- Symmetry and the bound are proof-irrelevant properties, not selected numerical data. -/
def boundedSymmetricSubalgebra (R : Type*) [CommRing R] : Subalgebra R (MvPowerSeries ℕ R) where
  carrier := {f | IsSymmetric f ∧ HasBoundedTotalDegree f}
  mul_mem' hf hg := ⟨(symmetricSubalgebra ℕ R).mul_mem hf.1 hg.1, hf.2.mul hg.2⟩
  add_mem' hf hg := ⟨(symmetricSubalgebra ℕ R).add_mem hf.1 hg.1, hf.2.add hg.2⟩
  algebraMap_mem' r := ⟨(symmetricSubalgebra ℕ R).algebraMap_mem r, hasBoundedTotalDegree_C r⟩

abbrev SymmetricSeries (R : Type*) [CommRing R] := ↥(symmetricSubalgebra ℕ R)
abbrev BoundedSymmetricSeries (R : Type*) [CommRing R] := ↥(boundedSymmetricSubalgebra R)

/-- Set every variable outside the initial finite alphabet to zero. -/
def finiteRestriction (R : Type*) [CommRing R] (N : ℕ) :
    MvPowerSeries ℕ R →ₐ[R] MvPowerSeries (Fin N) R :=
  MvPowerSeries.killCompl (Fin.valEmbedding : Fin N ↪ ℕ)

@[simp] theorem coeff_finiteRestriction (N : ℕ) (f : MvPowerSeries ℕ R) (a : Fin N →₀ ℕ) :
    MvPowerSeries.coeff a (finiteRestriction R N f) =
      MvPowerSeries.coeff (a.embDomain Fin.valEmbedding) f := rfl

/-- Every finitely supported exponent vector lies in an initial finite alphabet. -/
theorem exists_fin_exponent (a : ℕ →₀ ℕ) :
    ∃ (N : ℕ) (b : Fin N →₀ ℕ), b.embDomain Fin.valEmbedding = a := by
  classical
  let N := a.support.sup id + 1
  have ha : ↑a.support ⊆ Set.range (Fin.valEmbedding : Fin N ↪ ℕ) := by
    intro i hi
    exact ⟨⟨i, Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)⟩, rfl⟩
  exact ⟨N, a.comapDomain Fin.valEmbedding Fin.valEmbedding.injective.injOn,
    Finsupp.embDomain_comapDomain ha⟩

/-- All finite restrictions jointly detect a series, bounded or unbounded. -/
theorem eq_of_finiteRestriction_eq {f g : MvPowerSeries ℕ R}
    (h : ∀ N, finiteRestriction R N f = finiteRestriction R N g) : f = g := by
  apply MvPowerSeries.ext
  intro a
  obtain ⟨N, b, rfl⟩ := exists_fin_exponent a
  exact congrArg (MvPowerSeries.coeff b) (h N)

@[simp] theorem finiteRestriction_monomialSeries {d : ℕ} (N : ℕ) (μ : Nat.Partition d) :
    finiteRestriction R N (monomialSeries μ) =
      (MvPolynomial.msymm (Fin N) R μ : MvPowerSeries (Fin N) R) := by
  ext a
  simp [MvPolynomial.coeff_msymm]

/-- The Mathlib partition determined by an alphabet exponent vector. -/
def exponentPartition (a : σ →₀ ℕ) : Σ d, Nat.Partition d :=
  ⟨a.degree, ⟨exponentParts a, fun {_} => exponentParts_pos a, rfl⟩⟩

@[simp] theorem exponentPartition_parts (a : σ →₀ ℕ) :
    (exponentPartition a).2.parts = exponentParts a := rfl

@[simp] theorem exponentPartition_degree (a : σ →₀ ℕ) :
    (exponentPartition a).1 = a.degree := rfl

theorem exponentPartition_eq_iff (a : σ →₀ ℕ) (μ : Σ d, Nat.Partition d) :
    exponentPartition a = μ ↔ exponentParts a = μ.2.parts := by
  constructor
  · intro h
    exact congrArg (fun ν : Σ d, Nat.Partition d => ν.2.parts) h
  · intro h
    obtain ⟨d, μ⟩ := μ
    have hd : a.degree = d := (congrArg Multiset.sum h).trans μ.parts_sum
    subst d
    exact congrArg (Sigma.mk a.degree) (Nat.Partition.ext h)

theorem exponentPartition_eq_of_parts_eq {τ : Type*} (a : σ →₀ ℕ) (b : τ →₀ ℕ)
    (h : exponentParts a = exponentParts b) : exponentPartition a = exponentPartition b :=
  (exponentPartition_eq_iff a _).mpr h

/-- A representative of each partition in the countably infinite alphabet. -/
def representative (μ : Σ d, Nat.Partition d) : ℕ →₀ ℕ :=
  (Partition.representative μ.2).embDomain Fin.valEmbedding

@[simp] theorem exponentParts_representative (μ : Σ d, Nat.Partition d) :
    exponentParts (representative μ) = μ.2.parts := by simp [representative]

@[simp] theorem exponentPartition_representative (μ : Σ d, Nat.Partition d) :
    exponentPartition (representative μ) = μ :=
  (exponentPartition_eq_iff _ _).mpr (exponentParts_representative μ)

@[simp] theorem degree_representative (μ : Σ d, Nat.Partition d) :
    (representative μ).degree = μ.1 :=
  congrArg Sigma.fst (exponentPartition_representative μ)

end SymmetricFunctions.Series
