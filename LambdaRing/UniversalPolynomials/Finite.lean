import SymmetricFunctions.Finite.Weighted
import Mathlib.Data.Finset.Powerset

/-! # Elementary evaluation on finite alphabets

These constructions precede every lambda-ring structure. They are finite
polynomial expressions over arbitrary commutative semirings or rings.
-/

namespace LambdaRing.UniversalPolynomial

noncomputable section

open Finset

variable {σ τ A B : Type*} [CommSemiring A] [CommSemiring B]

/-- Elementary evaluation on a specified finite set of alphabet indices. -/
def elementaryOn (s : Finset σ) (x : σ → A) (n : ℕ) : A :=
  ∑ t ∈ s.powersetCard n, ∏ i ∈ t, x i

/-- Elementary evaluation on the whole finite alphabet. -/
def elementaryValue [Fintype σ] (x : σ → A) (n : ℕ) : A :=
  elementaryOn univ x n

@[simp] theorem elementaryOn_zero (s : Finset σ) (x : σ → A) :
    elementaryOn s x 0 = 1 := by simp [elementaryOn]

@[simp] theorem elementaryValue_zero [Fintype σ] (x : σ → A) :
    elementaryValue x 0 = 1 := elementaryOn_zero _ _

@[simp] theorem elementaryOn_one (s : Finset σ) (x : σ → A) :
    elementaryOn s x 1 = ∑ i ∈ s, x i := by simp [elementaryOn, powersetCard_one]

@[simp] theorem elementaryValue_one [Fintype σ] (x : σ → A) :
    elementaryValue x 1 = ∑ i, x i := elementaryOn_one _ _

@[simp] theorem map_elementaryOn (φ : A →+* B) (s : Finset σ) (x : σ → A) (n : ℕ) :
    φ (elementaryOn s x n) = elementaryOn s (φ ∘ x) n := by
  simp [elementaryOn]

@[simp] theorem map_elementaryValue [Fintype σ] (φ : A →+* B) (x : σ → A) (n : ℕ) :
    φ (elementaryValue x n) = elementaryValue (φ ∘ x) n :=
  map_elementaryOn φ _ x n

/-- Elementary values vanish beyond the number of available entries. -/
theorem elementaryValue_eq_zero_of_card_lt [Fintype σ] (x : σ → A) {n : ℕ}
    (hn : Fintype.card σ < n) : elementaryValue x n = 0 := by
  classical
  have hc : (univ : Finset σ).card < n := by simpa using hn
  rw [elementaryValue, elementaryOn, powersetCard_eq_empty.mpr hc, sum_empty]

/-- Renaming a finite alphabet along an embedding preserves elementary evaluation. -/
theorem elementaryOn_map (s : Finset σ) (f : σ ↪ τ) (y : τ → A) (n : ℕ) :
    elementaryOn (s.map f) y n = elementaryOn s (y ∘ f) n := by
  simp [elementaryOn, powersetCard_map]

/-- Removing alphabet entries with value zero does not change elementary evaluation. -/
theorem elementaryOn_subset {s t : Finset σ} (hst : s ⊆ t)
    (x : σ → A) (hz : ∀ i ∈ t, i ∉ s → x i = 0) (n : ℕ) :
    elementaryOn t x n = elementaryOn s x n := by
  classical
  symm
  apply Finset.sum_subset (powersetCard_mono hst)
  intro u hut hus
  have hu := (mem_powersetCard.mp hut)
  have hn : ¬ u ⊆ s := by
    intro h
    exact hus (mem_powersetCard.mpr ⟨h, hu.2⟩)
  obtain ⟨i, hiu, his⟩ := Finset.not_subset.mp hn
  exact Finset.prod_eq_zero hiu (hz i (hu.1 hiu) his)

/-- Adjoining any number of zero-valued entries leaves the elementary values unchanged. -/
theorem elementaryValue_extend [Fintype σ] [Fintype τ] (f : σ ↪ τ)
    (x : σ → A) (y : τ → A) (hxy : ∀ i, y (f i) = x i)
    (hz : ∀ j, j ∉ Set.range f → y j = 0) (n : ℕ) :
    elementaryValue y n = elementaryValue x n := by
  classical
  unfold elementaryValue
  rw [elementaryOn_subset (Finset.subset_univ (univ.map f)) y]
  · rw [elementaryOn_map]
    congr 1
    exact funext hxy
  · intro j _ hj
    apply hz j
    simpa using hj

/-- Finite alphabet reindexing, with no choice of ordering involved. -/
theorem elementaryValue_equiv [Fintype σ] [Fintype τ] (f : σ ≃ τ)
    (y : τ → A) (n : ℕ) : elementaryValue (y ∘ f) n = elementaryValue y n := by
  symm
  apply elementaryValue_extend f.toEmbedding (y ∘ f) y (fun _ => rfl)
  intro j hj
  exact False.elim (hj (f.surjective j))

/-- Agreement with Mathlib's elementary polynomial evaluated at alphabet entries. -/
theorem aeval_esymm [Fintype σ] {R : Type*} [CommSemiring R] [Algebra R A]
    (x : σ → A) (n : ℕ) :
    MvPolynomial.aeval x (MvPolynomial.esymm σ R n) = elementaryValue x n := by
  simp [MvPolynomial.esymm, elementaryValue, elementaryOn]

/-- Equal-degree alphabet entries give degree n*d at the nth elementary value. -/
theorem isHomogeneous_elementaryValue [Fintype σ] {R υ : Type*} [CommSemiring R]
    (x : σ → MvPolynomial υ R) (d n : ℕ) (hx : ∀ i, (x i).IsHomogeneous d) :
    (elementaryValue x n).IsHomogeneous (n * d) := by
  classical
  unfold elementaryValue elementaryOn
  apply (MvPolynomial.homogeneousSubmodule υ R (n * d)).sum_mem
  intro t ht
  have hh := MvPolynomial.IsHomogeneous.prod t x (fun _ => d) (fun i _ => hx i)
  simpa [(mem_powersetCard.mp ht).2] using hh

end

end LambdaRing.UniversalPolynomial
