import LambdaRing.Transport

/-! # Integral closure under exterior powers inside a subring

The elements whose exterior powers all lie in a subring themselves form a
subring. The negative-input argument uses additive cancellation, not division.
-/

noncomputable section

namespace LambdaRing

variable {A : Type*} [CommRing A]

/-- Evaluating an integral polynomial at subring elements stays in the subring. -/
theorem int_aeval_mem {σ : Type*} (S : Subring A) (x : σ → A)
    (hx : ∀ i, x i ∈ S) (p : MvPolynomial σ ℤ) : MvPolynomial.aeval x p ∈ S := by
  apply MvPolynomial.eval₂_mem
  · intro r _
    simp
  · exact hx

variable [PreLambdaRing A]

private theorem lambda_neg_mem (S : Subring A) {a : A}
    (ha : ∀ n, lambda n a ∈ S) (n : ℕ) : lambda n (-a) ∈ S := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; simp
    have he := lambda_neg_convolution n a
    rw [ite_eq_right hn, ← Finset.add_sum_erase _ _ (by simp : (0,n) ∈ Finset.antidiagonal n)] at he
    simp only [lambda_zero, one_mul] at he
    rw [eq_neg_of_add_eq_zero_left he]
    apply S.neg_mem
    apply S.sum_mem
    intro ij hij
    have hm := Finset.mem_erase.mp hij
    have hp := Finset.mem_antidiagonal.mp hm.2
    have hj : ij.2 < n := by
      by_contra h
      apply hm.1
      apply Prod.ext <;> omega
    exact S.mul_mem (ha _) (ih _ hj)

variable [SpecialLambdaRing A]

/-- The largest part of a subring closed under every exterior power. -/
def lambdaStableSubring (S : Subring A) : Subring A where
  carrier := {a | ∀ n, lambda n a ∈ S}
  zero_mem' n := by rw [lambda_zero_input]; split <;> simp
  one_mem' n := by rw [lambda_unit]; split <;> simp
  add_mem' ha hb n := by
    rw [lambda_add]
    exact S.sum_mem fun ij _ => S.mul_mem (ha ij.1) (hb ij.2)
  neg_mem' := lambda_neg_mem S
  mul_mem' ha hb n := by
    rw [lambda_mul]
    apply int_aeval_mem
    intro i
    cases i with
    | inl i => exact ha i
    | inr i => exact hb i

@[simp] theorem mem_lambdaStableSubring (S : Subring A) (a : A) :
    a ∈ lambdaStableSubring S ↔ ∀ n, lambda n a ∈ S := Iff.rfl

theorem lambdaStableSubring_le (S : Subring A) : lambdaStableSubring S ≤ S := by
  intro a ha
  simpa using ha 1

/-- The iteration identity closes the stable subring under exterior powers. -/
theorem lambda_mem_lambdaStableSubring (S : Subring A) {a : A}
    (ha : a ∈ lambdaStableSubring S) (m : ℕ) : lambda m a ∈ lambdaStableSubring S := by
  intro n
  rw [lambda_iterate]
  exact int_aeval_mem S _ (fun i : ℕ+ => ha i) _

end LambdaRing
