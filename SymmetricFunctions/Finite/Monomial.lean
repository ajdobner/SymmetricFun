import SymmetricFunctions.Stable
import SymmetricFunctions.Partition

/-! # Finite monomial symmetric polynomials and their coefficients

Reuse Mathlib's orbit sum `MvPolynomial.msymm`. Each exponent vector occurs once,
including shapes with repeated parts; no orbit cardinal is inverted.
-/

noncomputable section

namespace SymmetricFunctions

/-- The multiset of nonzero exponents, retaining repeated values. -/
def exponentParts {σ : Type*} (a : σ →₀ ℕ) : Multiset ℕ := a.support.val.map a

@[simp] theorem sum_exponentParts {σ : Type*} (a : σ →₀ ℕ) :
    (exponentParts a).sum = a.sum (fun _ n => n) := rfl

theorem exponentParts_pos {σ : Type*} (a : σ →₀ ℕ) {n : ℕ}
    (hn : n ∈ exponentParts a) : 0 < n := by
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hn
  exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)

@[simp] theorem card_exponentParts {σ : Type*} (a : σ →₀ ℕ) :
    (exponentParts a).card = a.support.card := Multiset.card_map _ _

@[simp] theorem exponentParts_toFinsupp {σ : Type*} [DecidableEq σ] {d : ℕ}
    (s : Sym σ d) : exponentParts (s : Multiset σ).toFinsupp = (Nat.Partition.ofSym s).parts := rfl

/-- A multiset of variables is the monomial of its multiplicity vector. -/
theorem prod_multiset_X {σ R : Type*} [DecidableEq σ] [CommSemiring R] (s : Multiset σ) :
    (s.map (MvPolynomial.X (R := R))).prod = MvPolynomial.monomial s.toFinsupp 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons i s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, ih]
    rw [show (i ::ₘ s).toFinsupp = Finsupp.single i 1 + s.toFinsupp by
      rw [← Multiset.singleton_add, map_add, Multiset.toFinsupp_singleton]]
    rw [add_comm, MvPolynomial.monomial_add_single]
    simp [mul_comm]

end SymmetricFunctions

namespace MvPolynomial

open SymmetricFunctions
variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R] {d : ℕ}

theorem msymm_eq_sum_monomials (μ : Nat.Partition d) :
    msymm σ R μ = ∑ s : {s : Sym σ d // Nat.Partition.ofSym s = μ},
      monomial (s.val : Multiset σ).toFinsupp 1 := by
  unfold msymm
  apply Finset.sum_congr rfl
  intro s _
  exact prod_multiset_X (s.val : Multiset σ)

/-- Finite monomial coefficients are the indicator of the partition shape. -/
theorem coeff_msymm (μ : Nat.Partition d) (a : σ →₀ ℕ) :
    (msymm σ R μ).coeff a = if exponentParts a = μ.parts then 1 else 0 := by
  classical
  rw [msymm_eq_sum_monomials, coeff_sum]
  by_cases ha : exponentParts a = μ.parts
  · rw [ite_eq_left ha]
    have hd : a.sum (fun _ n => n) = d := by
      rw [← sum_exponentParts, ha, μ.parts_sum]
    let s : Sym σ d := ⟨a.toMultiset, by
      simpa only [Finsupp.card_toMultiset, Function.id_def] using hd⟩
    have hs : Nat.Partition.ofSym s = μ := by
      apply Nat.Partition.ext
      rw [← exponentParts_toFinsupp]
      simpa [s] using ha
    let t : {s : Sym σ d // Nat.Partition.ofSym s = μ} := ⟨s, hs⟩
    rw [Finset.sum_eq_single t]
    · simp [t, s]
    · intro u _ hut
      rw [coeff_monomial]
      apply ite_eq_right
      intro he
      apply hut
      apply Subtype.ext
      apply Subtype.ext
      apply Multiset.toFinsupp.injective
      exact he.trans (by simp [t, s])
    · simp
  · rw [ite_eq_right ha]
    apply Finset.sum_eq_zero
    intro s _
    rw [coeff_monomial]
    apply ite_eq_right
    intro he
    apply ha
    rw [← he, exponentParts_toFinsupp, s.property]

end MvPolynomial

namespace SymmetricFunctions

@[simp] theorem exponentParts_zero {σ : Type*} : exponentParts (0 : σ →₀ ℕ) = 0 := by
  simp [exponentParts]

/-- Adding unused variables leaves the multiset of nonzero exponents unchanged. -/
@[simp] theorem exponentParts_embDomain {σ τ : Type*} (f : σ ↪ τ) (a : σ →₀ ℕ) :
    exponentParts (a.embDomain f) = exponentParts a := by
  classical
  simp [exponentParts]

end SymmetricFunctions

namespace MvPolynomial

open SymmetricFunctions
variable {σ τ R : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ]
variable [CommSemiring R] {d : ℕ}

/-- Deleting unused alphabet variables preserves finite monomial symmetric polynomials. -/
theorem killCompl_msymm (f : σ ↪ τ) (μ : Nat.Partition d) :
    killCompl (R := R) f.injective (msymm τ R μ) = msymm σ R μ := by
  ext a
  rw [coeff_killCompl, ← Finsupp.embDomain_eq_mapDomain, coeff_msymm,
    exponentParts_embDomain, coeff_msymm]

/-- The finite orbit sum is homogeneous of the partition's size. -/
theorem isHomogeneous_msymm (μ : Nat.Partition d) : (msymm σ R μ).IsHomogeneous d := by
  intro a ha
  have hc := ha
  rw [coeff_msymm] at hc
  have he : exponentParts a = μ.parts := by
    by_contra h
    simp [h] at hc
  simpa [Finsupp.weight_apply] using
    (sum_exponentParts a).symm.trans ((congrArg Multiset.sum he).trans μ.parts_sum)

/-- Too few letters give zero, even if the coefficient ring has torsion or is trivial. -/
theorem msymm_eq_zero_of_card_lt (μ : Nat.Partition d) (hμ : Fintype.card σ < μ.parts.card) :
    msymm σ R μ = 0 := by
  ext a
  rw [coeff_msymm]
  have h : exponentParts a ≠ μ.parts := by
    intro he
    have hc := congrArg Multiset.card he
    rw [card_exponentParts] at hc
    have := Finset.card_le_univ a.support
    omega
  simp [h]

end MvPolynomial

namespace SymmetricFunction

open MvPolynomial
variable (R : Type*) [CommRing R]

/-- The public last-zero transition is Mathlib's complement-deletion map. -/
theorem zeroLast_eq_killCompl (N : ℕ) :
    zeroLast R N = killCompl (R := R) (Fin.castSucc_injective (n := N)) := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [zeroLast, killCompl]
  · rw [zeroLast_X_castSucc, ← rename_X Fin.castSucc j, killCompl_rename_app]

/-- The finite monomial family is compatible at every alphabet size. -/
theorem zeroLast_msymm {d : ℕ} (N : ℕ) (μ : Nat.Partition d) :
    zeroLast R N (msymm (Fin (N+1)) R μ) = msymm (Fin N) R μ := by
  rw [zeroLast_eq_killCompl]
  exact killCompl_msymm Fin.castSuccEmb μ

end SymmetricFunction
