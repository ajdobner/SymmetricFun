import LambdaRing.UniversalPolynomials.ProductEvaluation
import LambdaRing.UniversalPolynomials.TwoAlphabetBounds

/-! # Geometric characterization and uniqueness of product polynomials -/

namespace LambdaRing.UniversalPolynomial

noncomputable section

open MvPolynomial

/-- Adjoining zero entries to the first alphabet leaves pair-product elementary values unchanged. -/
theorem pairProductValue_extend_left {σ υ τ A : Type*}
    [Fintype σ] [Fintype υ] [Fintype τ] [CommRing A]
    (f : σ ↪ υ) (x : σ → A) (z : υ → A) (y : τ → A)
    (hx : ∀ i, z (f i) = x i) (hz : ∀ j, j ∉ Set.range f → z j = 0) (n : ℕ) :
    elementaryValue (fun ij : υ × τ => z ij.1 * y ij.2) n =
      elementaryValue (fun ij : σ × τ => x ij.1 * y ij.2) n := by
  apply elementaryValue_extend (f.prodMap (Function.Embedding.refl τ))
  · intro ij
    exact congrArg (· * y ij.2) (hx ij.1)
  · intro ij hij
    have hzero : z ij.1 = 0 := hz ij.1 (by
      rintro ⟨i, hi⟩
      exact hij ⟨(i, ij.2), Prod.ext hi rfl⟩)
    simp [hzero]

/-- The corresponding zero-extension stability for the second alphabet. -/
theorem pairProductValue_extend_right {σ τ υ A : Type*}
    [Fintype σ] [Fintype τ] [Fintype υ] [CommRing A]
    (f : τ ↪ υ) (x : σ → A) (y : τ → A) (z : υ → A)
    (hy : ∀ j, z (f j) = y j) (hz : ∀ j, j ∉ Set.range f → z j = 0) (n : ℕ) :
    elementaryValue (fun ij : σ × υ => x ij.1 * z ij.2) n =
      elementaryValue (fun ij : σ × τ => x ij.1 * y ij.2) n := by
  apply elementaryValue_extend ((Function.Embedding.refl σ).prodMap f)
  · intro ij
    exact congrArg (x ij.1 * ·) (hy ij.2)
  · intro ij hij
    have hzero : z ij.2 = 0 := hz ij.2 (by
      rintro ⟨j, hj⟩
      exact hij ⟨(ij.1, j), Prod.ext rfl hj⟩)
    simp [hzero]

/-- The actual elementary polynomial of all pairwise products in two disjoint alphabets. -/
def pairProductPolynomial (σ τ R : Type*) [Fintype σ] [Fintype τ] [CommRing R] (n : ℕ) :
    MvPolynomial (σ ⊕ τ) R :=
  elementaryValue (fun ij : σ × τ => X (Sum.inl ij.1) * X (Sum.inr ij.2)) n

theorem pairProductPolynomial_eq_aeval (σ τ R : Type*) [Fintype σ] [Fintype τ] [CommRing R]
    (n : ℕ) : pairProductPolynomial σ τ R n =
      aeval (fun ij : σ × τ => X (R := R) (Sum.inl ij.1) * X (Sum.inr ij.2))
        (esymm (σ × τ) R n) := (aeval_esymm _ _).symm

private theorem elementaryValue_rename_X {σ υ R : Type*} [Fintype σ] [CommRing R]
    (f : σ → υ) (n : ℕ) :
    elementaryValue (fun i => X (R := R) (f i)) n = rename f (esymm σ R n) := by
  rw [rename_eq_aeval, aeval_esymm]
  rfl

/-- The integer product polynomial specializes correctly over every commutative ring. -/
theorem productPolynomial_specialize (σ τ R : Type*) [Fintype σ] [Fintype τ] [CommRing R]
    (n : ℕ) :
    aeval (Sum.elim (fun i : ℕ+ => rename Sum.inl (esymm σ R i))
      (fun j : ℕ+ => rename Sum.inr (esymm τ R j))) (productPolynomial n) =
        pairProductPolynomial σ τ R n := by
  have he := productPolynomial_eval (fun i : σ => X (R := R) (Sum.inl i))
    (fun j : τ => X (R := R) (Sum.inr j)) n
  simp only [elementaryValue_rename_X] at he
  exact he

/-- Sufficiently many variables in each alphabet uniquely determine the bounded expression. -/
theorem productPolynomial_unique (N M n : ℕ) (hN : n ≤ N) (hM : n ≤ M)
    (q : MvPolynomial (ℕ+ ⊕ ℕ+) ℤ)
    (hql : ∀ i, Sum.inl i ∈ q.vars → (i : ℕ) ≤ n)
    (hqr : ∀ j, Sum.inr j ∈ q.vars → (j : ℕ) ≤ n)
    (he : aeval (Sum.elim (fun i : ℕ+ => rename Sum.inl (esymm (Fin N) ℤ i))
      (fun j : ℕ+ => rename Sum.inr (esymm (Fin M) ℤ j))) q =
        pairProductPolynomial (Fin N) (Fin M) ℤ n) : q = productPolynomial n := by
  apply twoElementary_injective_of_vars_le ℤ N M
    (fun i hi => (hql i hi).trans hN) (fun j hj => (hqr j hj).trans hM)
    (fun i hi => (productPolynomial_vars_left_le n hi).trans hN)
    (fun j hj => (productPolynomial_vars_right_le n hj).trans hM)
  rw [he, productPolynomial_specialize]

/-- Discarding elementary indices beyond either sufficient bound changes nothing. -/
theorem productPolynomial_truncate (N M n : ℕ) (hN : n ≤ N) (hM : n ≤ M) :
    aeval (Sum.elim
      (fun i : ℕ+ => if (i : ℕ) ≤ N then X (Sum.inl i) else 0)
      (fun j : ℕ+ => if (j : ℕ) ≤ M then X (Sum.inr j) else 0)) (productPolynomial n) =
        productPolynomial n := by
  apply MvPolynomial.hom_congr_vars
    (f₁ := (aeval (R := ℤ) (Sum.elim
      (fun i : ℕ+ => if (i : ℕ) ≤ N then X (Sum.inl i) else 0)
      (fun j : ℕ+ => if (j : ℕ) ≤ M then X (Sum.inr j) else 0))).toRingHom)
    (f₂ := RingHom.id _) (p₁ := productPolynomial n) (p₂ := productPolynomial n)
  · ext r
    simp
  · intro k hk _
    cases k with
    | inl i => simp [(productPolynomial_vars_left_le n hk).trans hN]
    | inr j => simp [(productPolynomial_vars_right_le n hk).trans hM]
  · rfl

@[simp] theorem productPolynomial_zero : productPolynomial 0 = 1 := by
  symm
  apply productPolynomial_unique 0 0 0 le_rfl le_rfl 1
  · intro i hi
    simp at hi
  · intro j hj
    simp at hj
  · simp [pairProductPolynomial]

@[simp] theorem productPolynomial_one :
    productPolynomial 1 = X (Sum.inl (1 : ℕ+)) * X (Sum.inr (1 : ℕ+)) := by
  classical
  symm
  apply productPolynomial_unique 1 1 1 le_rfl le_rfl
    (X (Sum.inl (1 : ℕ+)) * X (Sum.inr (1 : ℕ+)))
  · intro i hi
    have hh := MvPolynomial.vars_mul (X (R := ℤ) (Sum.inl (1 : ℕ+)))
      (X (Sum.inr (1 : ℕ+))) hi
    have he : i = 1 := by simpa using hh
    simp [he]
  · intro j hj
    have hh := MvPolynomial.vars_mul (X (R := ℤ) (Sum.inl (1 : ℕ+)))
      (X (Sum.inr (1 : ℕ+))) hj
    have he : j = 1 := by simpa using hh
    simp [he]
  · simp [pairProductPolynomial, elementaryValue_one, MvPolynomial.esymm_one,
      Fintype.sum_prod_type]

/-- An empty first alphabet gives the zero positive-degree elementary value. -/
theorem pairProductPolynomial_empty_left (τ R : Type*) [Fintype τ] [CommRing R] (n : ℕ+) :
    pairProductPolynomial (Fin 0) τ R n = 0 := by
  apply elementaryValue_eq_zero_of_card_lt
  simp

/-- An empty second alphabet has the same boundary convention. -/
theorem pairProductPolynomial_empty_right (σ R : Type*) [Fintype σ] [CommRing R] (n : ℕ+) :
    pairProductPolynomial σ (Fin 0) R n = 0 := by
  apply elementaryValue_eq_zero_of_card_lt
  simp

section Examples

example : pairProductPolynomial (Fin 0) (Fin 0) ℤ 0 = 1 := by
  simp [pairProductPolynomial]

example : pairProductPolynomial (Fin 0) (Fin 0) ℤ 1 = 0 :=
  pairProductPolynomial_empty_left (Fin 0) ℤ 1

example {A : Type*} [CommRing A] (x y : ℕ+ → A) :
    aeval (Sum.elim x y) (productPolynomial 1) = x 1 * y 1 := by simp

end Examples

end

end LambdaRing.UniversalPolynomial
