import SymmetricFunctions.Finite.Generating
import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Integer matrices count complete-function coefficients

Rows record complete-function factors; columns record alphabet exponents.
Transposition exchanges the two margins, without dividing by any integer.
-/

noncomputable section
namespace SymmetricFunctions

variable {σ τ R : Type*} [Fintype σ] [Fintype τ] [CommRing R]

/-- Total degree in a finite alphabet is the sum of all entries, including zeros. -/
theorem finsupp_degree_eq_sum (a : σ →₀ ℕ) : a.degree = ∑ i, a i := by
  change a.sum (fun _ n => n) = _
  exact Finsupp.sum_fintype _ _ (fun _ => rfl)

open Classical in
/-- A complete polynomial has coefficient one at every exponent of its degree. -/
theorem coeff_hsymm (a : σ →₀ ℕ) (n : ℕ) :
    (MvPolynomial.hsymm σ R n).coeff a = if a.degree = n then 1 else 0 := by
  classical
  rw [hsymm_eq_sum_finsupp, MvPolynomial.coeff_sum]
  have hi (b : σ →₀ ℕ) : Finsupp.indicator Finset.univ (fun i _ => b i) = b := by
    ext i
    simp
  simp_rw [MvPolynomial.coeff_prod_X_pow, hi]
  simp only [Finset.sum_ite_eq, Finset.mem_finsuppAntidiag, Finset.subset_univ,
    and_true, ← finsupp_degree_eq_sum]

open Classical in
/-- Finite nonnegative integer matrices with the specified row and column sums. -/
def marginMatrices (a : σ →₀ ℕ) (b : τ →₀ ℕ) : Finset (σ →₀ τ →₀ ℕ) :=
  (Finset.finsuppAntidiag Finset.univ b).filter (fun A => ∀ i, (A i).degree = a i)

/-- Transpose of a matrix stored as finitely supported rows. -/
def transposeRows (A : σ →₀ τ →₀ ℕ) : τ →₀ σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => Finsupp.equivFunOnFinite.symm (fun i => A i j))

@[simp] theorem transposeRows_apply (A : σ →₀ τ →₀ ℕ) (j : τ) (i : σ) :
    transposeRows A j i = A i j := rfl

@[simp] theorem transposeRows_transposeRows (A : σ →₀ τ →₀ ℕ) :
    transposeRows (transposeRows A) = A := by
  ext i j
  rfl

/-- Membership spells out both margin constraints entry by entry. -/
theorem mem_marginMatrices (a : σ →₀ ℕ) (b : τ →₀ ℕ) (A : σ →₀ τ →₀ ℕ) :
    A ∈ marginMatrices a b ↔ (∀ j, ∑ i, A i j = b j) ∧ (∀ i, ∑ j, A i j = a i) := by
  classical
  simp only [marginMatrices, Finset.mem_filter, Finset.mem_finsuppAntidiag,
    Finset.subset_univ, and_true, Finsupp.ext_iff, Finsupp.finsetSum_apply,
    finsupp_degree_eq_sum]

/-- Matrix transpose exchanges the margins, including empty index types. -/
theorem transposeRows_mem_marginMatrices (a : σ →₀ ℕ) (b : τ →₀ ℕ)
    (A : σ →₀ τ →₀ ℕ) : transposeRows A ∈ marginMatrices b a ↔ A ∈ marginMatrices a b := by
  simp only [mem_marginMatrices, transposeRows_apply, and_comm]

/-- The integral count is symmetric in its two margins. -/
theorem card_marginMatrices_comm (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    (marginMatrices a b).card = (marginMatrices b a).card := by
  classical
  apply Finset.card_bij (fun A _ => transposeRows A)
  · intro A hA
    exact (transposeRows_mem_marginMatrices a b A).mpr hA
  · intro A hA B hB he
    simpa only [transposeRows_transposeRows] using congrArg transposeRows he
  · intro B hB
    exact ⟨transposeRows B, (transposeRows_mem_marginMatrices b a B).mpr hB,
      transposeRows_transposeRows B⟩

open Classical in
/-- Complete products count these matrices over every coefficient ring. -/
theorem coeff_prod_hsymm (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    (∏ i, MvPolynomial.hsymm τ R (a i)).coeff b = (marginMatrices a b).card := by
  classical
  rw [← MvPolynomial.coeff_coe]
  change MvPowerSeries.coeff b (MvPolynomial.coeToMvPowerSeries.ringHom
    (∏ i, MvPolynomial.hsymm τ R (a i))) = _
  rw [map_prod]
  rw [MvPowerSeries.coeff_prod]
  change (∑ A ∈ Finset.finsuppAntidiag Finset.univ b,
    ∏ i : σ, (MvPolynomial.hsymm τ R (a i)).coeff (A i)) = _
  simp only [coeff_hsymm]
  have hp (A : σ →₀ τ →₀ ℕ) :
      (∏ i : σ, (if (A i).degree = a i then 1 else 0 : R)) =
        if ∀ i, (A i).degree = a i then 1 else 0 := by
    split_ifs with h
    · simp [h]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  simp_rw [hp]
  simp [marginMatrices, Finset.sum_boole]

end SymmetricFunctions
