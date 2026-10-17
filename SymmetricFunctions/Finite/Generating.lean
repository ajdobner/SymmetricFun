import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

/-!
# Finite elementary and complete generating series

Univariate formal series are used here to prove finite coefficient identities.
They do not change the bounded-degree definition of symmetric functions.
-/

namespace SymmetricFunctions

noncomputable section

open Finset

variable (σ R : Type*) [Fintype σ] [DecidableEq σ] [CommRing R]

/-- The finite product with coefficients the signed elementary polynomials. -/
def elementarySeries : PowerSeries (MvPolynomial σ R) :=
  ∏ i : σ, (1 - PowerSeries.C (MvPolynomial.X i) * PowerSeries.X)

/-- The product of geometric series in the alphabet variables. -/
def completeSeries : PowerSeries (MvPolynomial σ R) :=
  ∏ i : σ, PowerSeries.mk (fun n => MvPolynomial.X i ^ n)

private theorem prod_map_eq_prod_count {α A : Type*} [Fintype α] [DecidableEq α] [CommMonoid A]
    (s : Multiset α) (x : α → A) : (s.map x).prod = ∏ i, x i ^ s.count i := by
  classical
  rw [Finset.prod_multiset_map_count]
  simpa only [Finsupp.prod, Multiset.toFinsupp_support, Multiset.toFinsupp_apply] using
    s.toFinsupp.prod_pow x

theorem hsymm_eq_sum_finsupp (n : ℕ) :
    MvPolynomial.hsymm σ R n =
      ∑ a ∈ Finset.finsuppAntidiag (Finset.univ : Finset σ) n,
        ∏ i : σ, MvPolynomial.X i ^ a i := by
  classical
  unfold MvPolynomial.hsymm
  refine Finset.sum_bij (fun s _ => s.val.toFinsupp) ?_ ?_ ?_ ?_
  · intro s _
    rw [Finset.mem_finsuppAntidiag']
    exact ⟨(Multiset.toFinsupp_sum_eq s.val).trans s.property, Finset.subset_univ _⟩
  · intro s _ t _ he
    apply Subtype.ext
    exact Multiset.toFinsupp.injective he
  · intro a ha
    refine ⟨⟨a.toMultiset, ?_⟩, Finset.mem_univ _, ?_⟩
    · rw [Finsupp.card_toMultiset]
      exact (Finset.mem_finsuppAntidiag'.mp ha).1
    · exact Finsupp.toMultiset_toFinsupp a
  · intro s _
    exact prod_map_eq_prod_count s.val MvPolynomial.X

@[simp] theorem coeff_completeSeries (n : ℕ) :
    PowerSeries.coeff n (completeSeries σ R) = MvPolynomial.hsymm σ R n := by
  classical
  rw [completeSeries, PowerSeries.coeff_prod, hsymm_eq_sum_finsupp]
  simp

omit [DecidableEq σ] in
@[simp] theorem coeff_elementarySeries (n : ℕ) :
    PowerSeries.coeff n (elementarySeries σ R) =
      (-1 : MvPolynomial σ R) ^ n * MvPolynomial.esymm σ R n := by
  classical
  have he (i : σ) : (1 - PowerSeries.C (MvPolynomial.X i) * PowerSeries.X) =
      1 + PowerSeries.monomial 1 (-MvPolynomial.X (R := R) i) := by
    apply PowerSeries.ext
    intro k
    by_cases hk : k = 1 <;>
      simp [PowerSeries.coeff_monomial, PowerSeries.coeff_C_mul, PowerSeries.coeff_X,
        sub_eq_add_neg, hk]
  simp_rw [elementarySeries, he]
  rw [Finset.prod_one_add, map_sum]
  simp_rw [PowerSeries.prod_monomial, Finset.sum_const, smul_eq_mul, mul_one,
    PowerSeries.coeff_monomial]
  rw [← Finset.sum_filter]
  have hfilter : (Finset.univ : Finset σ).powerset.filter (fun t => n = t.card) =
      Finset.univ.powersetCard n := by
    ext t
    simp [eq_comm]
  rw [hfilter, MvPolynomial.esymm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.prod_neg, (Finset.mem_powersetCard.mp ht).2]

private theorem geometric_mul_linear {A : Type*} [CommRing A] (a : A) :
    PowerSeries.mk (fun n => a ^ n) * (1 - PowerSeries.C a * PowerSeries.X) = 1 := by
  have he := congrArg (PowerSeries.rescale a) (PowerSeries.mk_one_mul_one_sub_eq_one A)
  simpa [PowerSeries.rescale_mk, PowerSeries.rescale_X] using he

omit [DecidableEq σ] in
theorem completeSeries_mul_elementarySeries :
    completeSeries σ R * elementarySeries σ R = 1 := by
  classical
  rw [completeSeries, elementarySeries, ← Finset.prod_mul_distrib]
  simp only [geometric_mul_linear, Finset.prod_const_one]

/-- The finite elementary/complete inverse identity, valid over every commutative ring. -/
theorem esymm_hsymm_convolution (n : ℕ) :
    ∑ ij ∈ antidiagonal n,
      (-1 : MvPolynomial σ R) ^ ij.1 * MvPolynomial.esymm σ R ij.1 *
        MvPolynomial.hsymm σ R ij.2 = if n = 0 then 1 else 0 := by
  have he : elementarySeries σ R * completeSeries σ R = 1 := by
    rw [mul_comm, completeSeries_mul_elementarySeries]
  have hc := congrArg (PowerSeries.coeff n) he
  simpa only [PowerSeries.coeff_mul, coeff_elementarySeries, coeff_completeSeries,
    PowerSeries.coeff_one] using hc

/-- The finite complete recurrence in the same integral convention as the public h family. -/
theorem hsymm_succ (n : ℕ) :
    MvPolynomial.hsymm σ R (n + 1) =
      ∑ ij ∈ antidiagonal n,
        (-1 : MvPolynomial σ R) ^ ij.1 * MvPolynomial.esymm σ R (ij.1 + 1) *
          MvPolynomial.hsymm σ R ij.2 := by
  have hc := esymm_hsymm_convolution σ R (n + 1)
  rw [Finset.Nat.sum_antidiagonal_succ] at hc
  simp only [pow_zero, MvPolynomial.esymm_zero, one_mul, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ↓reduceIte] at hc
  simp only [pow_succ, mul_neg_one, neg_mul, Finset.sum_neg_distrib] at hc
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hc)

end

end SymmetricFunctions
