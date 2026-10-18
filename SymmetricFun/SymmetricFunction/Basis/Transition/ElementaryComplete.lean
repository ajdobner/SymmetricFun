module

public import SymmetricFun.SymmetricFunction.Basis.Defs
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The elementary–complete relation

The alternating convolution of the elementary and complete homogeneous symmetric
functions is one in degree zero and zero in every positive degree.
The identity holds over a commutative ring for any variable type.

Coefficientwise, the squarefree divisors of a monomial correspond to subsets of
its support. Their alternating sum is the expansion of a product of copies of
`1 + (-1)`, which vanishes for every nonconstant monomial.
-/

@[expose] public section
noncomputable section

namespace MvPowerSeries

variable {σ : Type*} (R : Type*) [CommRing R]

private theorem sum_antidiagonal_squarefree [DecidableEq σ] (d : σ →₀ ℕ) :
    (∑ p ∈ Finset.antidiagonal d,
      if ∀ i ∈ p.1.support, p.1 i = 1 then (-1 : R) ^ p.1.support.card else 0) =
      ∑ s ∈ d.support.powerset, (-1 : R) ^ s.card := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun p _ => p.1.support) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro p hp
    apply Finset.mem_powerset.mpr
    apply Finsupp.support_mono
    rw [← Finset.mem_antidiagonal.mp (Finset.mem_filter.mp hp).1]
    exact le_self_add
  · intro p hp q hq hpq
    obtain ⟨hpadd, hpsq⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqadd, hqsq⟩ := Finset.mem_filter.mp hq
    have hfst : p.1 = q.1 := by
      ext i
      by_cases hi : i ∈ p.1.support
      · rw [hpsq i hi, hqsq i (hpq ▸ hi)]
      · rw [Finsupp.notMem_support_iff.mp hi,
          Finsupp.notMem_support_iff.mp (hpq ▸ hi)]
    apply Prod.ext hfst
    replace hpadd := Finset.mem_antidiagonal.mp hpadd
    rw [hfst] at hpadd
    exact add_left_cancel (hpadd.trans (Finset.mem_antidiagonal.mp hqadd).symm)
  · intro s hs
    let a : σ →₀ ℕ := Finsupp.indicator s (fun _ _ => 1)
    have hsupp : a.support = s := by
      ext i
      simp [a, Finsupp.mem_support_iff, Finsupp.indicator_apply]
    have ha : a ≤ d := by
      intro i
      by_cases hi : i ∈ s
      · simpa [a, Finsupp.indicator_of_mem hi] using
          Nat.succ_le_of_lt
            (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (Finset.mem_powerset.mp hs hi)))
      · simp [a, Finsupp.indicator_of_notMem hi]
    refine ⟨(a, d - a), Finset.mem_filter.mpr ⟨?_, ?_⟩, hsupp⟩
    · exact Finset.mem_antidiagonal.mpr (add_tsub_cancel_of_le ha)
    · intro i hi
      exact Finsupp.indicator_of_mem (hsupp ▸ hi) _

private theorem sum_antidiagonal_squarefree_eq_zero [DecidableEq σ]
    (d : σ →₀ ℕ) (hd : d ≠ 0) :
    (∑ p ∈ Finset.antidiagonal d,
      if ∀ i ∈ p.1.support, p.1 i = 1 then (-1 : R) ^ p.1.support.card else 0) = 0 := by
  classical
  rw [sum_antidiagonal_squarefree]
  have h := Finset.prod_add_one (f := fun _ : σ => (-1 : R)) d.support
  have hcard : d.support.card ≠ 0 :=
    Finset.card_ne_zero.mpr (Finsupp.support_nonempty_iff.mpr hd)
  simpa [Finset.prod_const, hcard] using h.symm

variable (σ)

/-- The alternating elementary–complete convolution is concentrated in degree zero. -/
theorem sum_antidiagonal_esymm_hsymm (n : ℕ) :
    (∑ p ∈ Finset.antidiagonal n,
      (-1 : R) ^ p.1 • (esymm σ R p.1 * hsymm σ R p.2)) =
      if n = 0 then 1 else 0 := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  rw [ite_eq_right hn]
  ext d
  rw [map_zero]
  by_cases hd : d.degree = n
  · simp only [map_sum, coeff_smul, coeff_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ q ∈ Finset.antidiagonal d,
          if ∀ i ∈ q.1.support, q.1 i = 1 then (-1 : R) ^ q.1.support.card else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        have hdegree : q.1.degree + q.2.degree = n := by
          rw [← map_add, Finset.mem_antidiagonal.mp hq, hd]
        rw [Finset.sum_eq_single_of_mem (q.1.degree, q.2.degree)
          (Finset.mem_antidiagonal.mpr hdegree)]
        · by_cases hsq : ∀ i ∈ q.1.support, q.1 i = 1
          · have hcard : q.1.degree = q.1.support.card := by
              simp only [Finsupp.degree_apply, Finset.sum_congr rfl hsq,
                Finset.sum_const, smul_eq_mul, mul_one]
            rw [coeff_esymm, coeff_hsymm, ite_eq_left ⟨hcard.symm, hsq⟩,
              ite_eq_left rfl, ite_eq_left hsq]
            simp only [mul_one, hcard]
          · simp only [coeff_esymm, hsq, and_false, ite_false, zero_mul, mul_zero]
        · intro p hp hne
          by_cases hfst : q.1.degree = p.1
          · have hsnd : q.2.degree ≠ p.2 := by
              intro hsnd
              exact hne (Prod.ext hfst.symm hsnd.symm)
            rw [IsHomogeneous.coeff_eq_zero (isHomogeneous_hsymm σ R p.2) hsnd,
              mul_zero, mul_zero]
          · rw [IsHomogeneous.coeff_eq_zero (isHomogeneous_esymm σ R p.1) hfst,
              zero_mul, mul_zero]
      _ = 0 := sum_antidiagonal_squarefree_eq_zero R d (by
        intro h
        subst d
        exact hn (by simpa using hd.symm))
  · rw [map_sum]
    apply Finset.sum_eq_zero
    intro p hp
    rw [coeff_smul]
    have hhom : IsHomogeneous (esymm σ R p.1 * hsymm σ R p.2) (p.1 + p.2) :=
      IsHomogeneous.mul (isHomogeneous_esymm σ R p.1) (isHomogeneous_hsymm σ R p.2)
    rw [Finset.mem_antidiagonal.mp hp] at hhom
    rw [hhom.coeff_eq_zero hd, mul_zero]

/-- The elementary–complete relation in positive degree. -/
theorem sum_antidiagonal_esymm_hsymm_eq_zero {n : ℕ} (hn : 0 < n) :
    (∑ p ∈ Finset.antidiagonal n,
      (-1 : R) ^ p.1 • (esymm σ R p.1 * hsymm σ R p.2)) = 0 := by
  rw [sum_antidiagonal_esymm_hsymm, ite_eq_right hn.ne']

/-- The elementary–complete relation, indexed by the elementary degree. -/
theorem sum_range_esymm_hsymm_eq_zero {n : ℕ} (hn : 0 < n) :
    (∑ i ∈ Finset.range (n + 1),
      (-1 : R) ^ i • (esymm σ R i * hsymm σ R (n - i))) = 0 := by
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (-1 : R) ^ i • (esymm σ R i * hsymm σ R j)) n).symm.trans
      (sum_antidiagonal_esymm_hsymm_eq_zero σ R hn)

end MvPowerSeries
