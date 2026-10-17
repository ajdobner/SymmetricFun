import SymmetricFunctions.Finite.Monomial
import Mathlib.Data.Multiset.Fintype
import Mathlib.Logic.Equiv.Fintype

/-! # Exponent orbits and partition representatives

Equal nonzero-exponent multisets classify permutation orbits. The fiber-matching
idea was inspected in ajdobner/SymmetricFun, SymmetricPoly/Finsupp/SymmetricAction.lean
at 98938de95a12b3ed363653cb980588e2a9188cb8. The proofs here are reconstructed
with Mathlib's partition, finite-fiber and support APIs; no draft definition is imported.
-/

noncomputable section

namespace SymmetricFunctions

private theorem exponentParts_count {σ : Type*} (a : σ →₀ ℕ) (n : ℕ) :
    (exponentParts a).count n = Fintype.card {i : a.support // a i = n} := by
  classical
  have hc : (a.support.filter (fun i => n = a i)).card =
      (a.support.attach.filter (fun i => n = a i.val)).card := by
    rw [Finset.filter_attach (fun i => n = a i), Finset.card_map, Finset.card_attach]
  simpa [exponentParts, Multiset.count_map, ← Finset.filter_val,
    Fintype.card_subtype, eq_comm] using hc

/-- Equal exponent shapes give a permutation matching every exponent, including zeros. -/
theorem exists_perm_of_exponentParts_eq {σ : Type*} {a b : σ →₀ ℕ}
    (h : exponentParts a = exponentParts b) :
    ∃ e : Equiv.Perm σ, ∀ i, b (e i) = a i := by
  classical
  have hc (n : ℕ) : Fintype.card {i : a.support // a i = n} =
      Fintype.card {i : b.support // b i = n} := by
    rw [← exponentParts_count, ← exponentParts_count, h]
  let fibers (n : ℕ) : {i : a.support // a i = n} ≃ {i : b.support // b i = n} :=
    Fintype.equivOfCardEq (hc n)
  let e : a.support ≃ b.support := Equiv.ofFiberEquiv fibers
  refine ⟨e.extendSubtype, fun i => ?_⟩
  by_cases hi : i ∈ a.support
  · rw [Equiv.extendSubtype_apply_of_mem e i hi]
    exact Equiv.ofFiberEquiv_map fibers ⟨i, hi⟩
  · rw [Finsupp.notMem_support_iff.mp hi,
      Finsupp.notMem_support_iff.mp (e.extendSubtype_not_mem i hi)]

/-- The corresponding equality of finitely supported exponent vectors. -/
theorem exists_mapDomain_eq_of_exponentParts_eq {σ : Type*} {a b : σ →₀ ℕ}
    (h : exponentParts a = exponentParts b) : ∃ e : Equiv.Perm σ, a.mapDomain e = b := by
  obtain ⟨e, he⟩ := exists_perm_of_exponentParts_eq h
  refine ⟨e, ?_⟩
  rw [← Finsupp.equivMapDomain_eq_mapDomain]
  ext i
  simpa only [Finsupp.equivMapDomain_apply, Equiv.apply_symm_apply] using (he (e.symm i)).symm

/-- Symmetry says that finite coefficients depend only on exponent shape. -/
theorem coeff_eq_of_exponentParts_eq {σ R : Type*} [CommSemiring R]
    {f : MvPolynomial σ R} (hf : f.IsSymmetric) {a b : σ →₀ ℕ}
    (h : exponentParts a = exponentParts b) : f.coeff a = f.coeff b := by
  obtain ⟨e, he⟩ := exists_mapDomain_eq_of_exponentParts_eq h
  have hc := MvPolynomial.coeff_rename_mapDomain e e.injective f a
  rw [he, hf e] at hc
  exact hc.symm

namespace Partition

/-- Every partition has a representative exponent vector in any sufficiently large alphabet. -/
theorem exists_exponentParts {σ : Type*} [Fintype σ] {d : ℕ} (μ : Nat.Partition d)
    (hμ : μ.parts.card ≤ Fintype.card σ) : ∃ a : σ →₀ ℕ, exponentParts a = μ.parts := by
  classical
  obtain ⟨e⟩ : Nonempty (μ.parts ↪ σ) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hμ)
  let a : μ.parts →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => (i : ℕ))
  have hs : a.support = Finset.univ := by
    ext i
    simp only [Finset.mem_univ, iff_true, Finsupp.mem_support_iff]
    exact Nat.ne_of_gt (μ.parts_pos (Multiset.coe_mem (x := i)))
  refine ⟨a.embDomain e, ?_⟩
  rw [exponentParts_embDomain, exponentParts, hs]
  exact Multiset.map_univ_coe μ.parts

/-- Positive parts imply that their number is at most the partition size. -/
theorem parts_card_le {d : ℕ} (μ : Nat.Partition d) : μ.parts.card ≤ d := by
  classical
  calc
    μ.parts.card = ∑ _i : μ.parts, 1 := by simp
    _ ≤ ∑ i : μ.parts, (i : ℕ) :=
      Finset.sum_le_sum fun i _ => μ.parts_pos (Multiset.coe_mem (x := i))
    _ = μ.parts.sum := (Multiset.sum_eq_sum_coe _).symm
    _ = d := μ.parts_sum

/-- A fixed exponent representative in the stable alphabet of size d.
Coordinates will be independent of this choice by symmetry. -/
def representative {d : ℕ} (μ : Nat.Partition d) : Fin d →₀ ℕ :=
  Classical.choose (exists_exponentParts μ (by simpa using parts_card_le μ))

@[simp] theorem exponentParts_representative {d : ℕ} (μ : Nat.Partition d) :
    exponentParts (representative μ) = μ.parts :=
  Classical.choose_spec (exists_exponentParts μ (by simpa using parts_card_le μ))

@[simp] theorem sum_representative {d : ℕ} (μ : Nat.Partition d) :
    (representative μ).sum (fun _ n => n) = d := by
  rw [← sum_exponentParts, exponentParts_representative, μ.parts_sum]

end Partition
end SymmetricFunctions

namespace MvPolynomial

open SymmetricFunctions

/-- A homogeneous symmetric polynomial expands by its exponent-shape coefficients.
Any choice of one exponent representative per partition gives the same formula. -/
theorem eq_sum_msymm_of_representatives {σ R : Type*} [Fintype σ] [DecidableEq σ]
    [CommSemiring R] {d : ℕ} (f : MvPolynomial σ R) (hs : f.IsSymmetric)
    (hd : f.IsHomogeneous d) (r : Nat.Partition d → σ →₀ ℕ)
    (hr : ∀ μ, exponentParts (r μ) = μ.parts) :
    f = ∑ μ : Nat.Partition d, f.coeff (r μ) • msymm σ R μ := by
  classical
  ext a
  rw [coeff_sum]
  simp only [coeff_smul, smul_eq_mul, coeff_msymm]
  by_cases ha : a.sum (fun _ n => n) = d
  · let μ : Nat.Partition d :=
      ⟨exponentParts a, fun {_} => exponentParts_pos a, (sum_exponentParts a).trans ha⟩
    have hshape : exponentParts a = μ.parts := rfl
    have hc : f.coeff a = f.coeff (r μ) :=
      coeff_eq_of_exponentParts_eq hs (hshape.trans (hr μ).symm)
    rw [Finset.sum_eq_single μ, ite_eq_left hshape, mul_one]
    · exact hc
    · intro ν _ hν
      have hn : exponentParts a ≠ ν.parts := by
        intro he
        exact hν (Nat.Partition.ext (hshape.symm.trans he)).symm
      rw [ite_eq_right hn, mul_zero]
    · simp
  · have hc : f.coeff a = 0 := by
      by_contra hc
      apply ha
      simpa [Finsupp.weight_apply] using hd hc
    rw [hc]
    symm
    apply Finset.sum_eq_zero
    intro μ _
    have hshape : exponentParts a ≠ μ.parts := by
      intro he
      apply ha
      exact (sum_exponentParts a).symm.trans ((congrArg Multiset.sum he).trans μ.parts_sum)
    rw [ite_eq_right hshape, mul_zero]

end MvPolynomial
