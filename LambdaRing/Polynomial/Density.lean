import LambdaRing.Polynomial.Rational
import LambdaRing.Polynomial.Positive
import Mathlib.Algebra.MvPolynomial.Funext

/-! # Polynomial density of nonnegative integer coefficient parameters -/

noncomputable section

namespace LambdaRing.Polynomial

open MvPolynomial UniversalPolynomial

variable {σ ι : Type*}

/-- Ring maps commute with evaluation of integral universal polynomials. -/
theorem map_int_aeval {A B κ : Type*} [CommRing A] [CommRing B]
    [Algebra ℤ A] [Algebra ℤ B] (φ : A →+* B) (x : κ → A) (p : MvPolynomial κ ℤ) :
    φ (aeval x p) = aeval (fun i => φ (x i)) p :=
  comp_aeval_apply x
    ({ φ with commutes' := fun z => by simp } : A →ₐ[ℤ] B) p

/-- The same evaluation formula with the two product-variable blocks kept explicit. -/
theorem map_int_aeval_sum {A B κ υ : Type*} [CommRing A] [CommRing B]
    [Algebra ℤ A] [Algebra ℤ B] (φ : A →+* B) (x : κ → A) (y : υ → A) (p : MvPolynomial (κ ⊕ υ) ℤ) :
    φ (aeval (Sum.elim x y) p) =
      aeval (Sum.elim (fun i => φ (x i)) (fun j => φ (y j))) p := by
  rw [map_int_aeval]
  apply congrArg (fun v : κ ⊕ υ → B => aeval v p)
  funext i
  cases i <;> rfl

/-- Naturals are an infinite testing set for rational polynomial identities. -/
theorem eq_of_eval_nat {p q : MvPolynomial ι ℚ}
    (h : ∀ a : ι → ℕ, eval (fun i => (a i : ℚ)) p = eval (fun i => (a i : ℚ)) q) : p = q := by
  apply MvPolynomial.funext_set (fun _ => Set.range (Nat.cast : ℕ → ℚ))
    (fun _ => Set.infinite_range_of_injective Nat.cast_injective)
  intro x hx
  have hnat : ∀ i, ∃ n : ℕ, (n : ℚ) = x i := fun i => hx i (Set.mem_univ i)
  choose a ha using hnat
  have he : (fun i => (a i : ℚ)) = x := funext ha
  simpa only [he] using h a

/-- Test a polynomial in alphabet variables by all natural coefficient-parameter values. -/
theorem eq_of_map_eval_nat {p q : MvPolynomial σ (MvPolynomial ι ℚ)}
    (h : ∀ a : ι → ℕ,
      map (eval (fun i => (a i : ℚ))) p = map (eval (fun i => (a i : ℚ))) q) : p = q := by
  apply MvPolynomial.ext
  intro m
  apply eq_of_eval_nat
  intro a
  have he := congrArg (fun f : MvPolynomial σ ℚ => f.coeff m) (h a)
  simpa only [coeff_map] using he

/-- A finite polynomial with independent indeterminates in its coefficient slots. -/
def parameterPolynomial (s : Finset (σ →₀ ℕ)) (tag : (σ →₀ ℕ) → ι) :
    MvPolynomial σ (MvPolynomial ι ℚ) := ∑ m ∈ s, monomial m (X (tag m))

/-- Specializing coefficient slots gives precisely the selected finite polynomial sum. -/
theorem map_parameterPolynomial (s : Finset (σ →₀ ℕ)) (tag : (σ →₀ ℕ) → ι)
    (a : ι → ℚ) : map (eval a) (parameterPolynomial s tag) =
      ∑ m ∈ s, monomial m (a (tag m)) := by
  classical
  simp [parameterPolynomial]

/-- Natural parameter values specialize to integral polynomials with natural coefficients. -/
theorem map_parameterPolynomial_nat (s : Finset (σ →₀ ℕ)) (tag : (σ →₀ ℕ) → ι)
    (a : ι → ℕ) : map (eval (fun i => (a i : ℚ))) (parameterPolynomial s tag) =
      map (Int.castRingHom ℚ) (∑ m ∈ s, monomial m (a (tag m) : ℤ)) := by
  rw [map_parameterPolynomial]
  simp

/-- Product identity for rational images of natural-coefficient sums. -/
theorem rationalOperation_mul_natSum (s t : Finset (σ →₀ ℕ))
    (a b : (σ →₀ ℕ) → ℕ) (n : ℕ) :
    rationalOperation n ((∑ m ∈ s, monomial m (a m : ℚ)) *
      ∑ m ∈ t, monomial m (b m : ℚ)) =
      aeval (Sum.elim
        (fun k : ℕ+ => rationalOperation k (∑ m ∈ s, monomial m (a m : ℚ)))
        (fun k : ℕ+ => rationalOperation k (∑ m ∈ t, monomial m (b m : ℚ))))
        (productPolynomial n) := by
  have h := congrArg (map (Int.castRingHom ℚ)) (operation_mul_natSum s t a b n)
  rw [map_operation_eq_rationalOperation, map_mul, map_int_aeval_sum (map (Int.castRingHom ℚ))] at h
  simp only [map_operation_eq_rationalOperation, map_sum, map_monomial,
    map_natCast] at h
  exact h

/-- Iteration identity for rational images of natural-coefficient sums. -/
theorem rationalOperation_iterate_natSum (s : Finset (σ →₀ ℕ))
    (a : (σ →₀ ℕ) → ℕ) (n m : ℕ) :
    rationalOperation n (rationalOperation m (∑ d ∈ s, monomial d (a d : ℚ))) =
      aeval (fun k : ℕ+ => rationalOperation k (∑ d ∈ s, monomial d (a d : ℚ)))
        (iterationPolynomial n m) := by
  have h := congrArg (map (Int.castRingHom ℚ)) (operation_iterate_natSum s a n m)
  rw [map_operation_eq_rationalOperation, map_operation_eq_rationalOperation,
    map_int_aeval (map (Int.castRingHom ℚ))] at h
  simp only [map_operation_eq_rationalOperation, map_sum, map_monomial,
    map_natCast] at h
  exact h

/-- The auxiliary recurrence commutes with evaluating rational coefficient parameters. -/
theorem map_eval_rationalOperation (a : ι → ℚ) (n : ℕ)
    (f : MvPolynomial σ (MvPolynomial ι ℚ)) :
    map (eval a) (rationalOperation n f) = rationalOperation n (map (eval a) f) :=
  rationalOperation_map (aeval a) n f

/-- Product identity with independent polynomial coefficient parameters. -/
theorem rationalOperation_mul_parameter (s t : Finset (σ →₀ ℕ))
    (tag₁ tag₂ : (σ →₀ ℕ) → ι) (n : ℕ) :
    rationalOperation n (parameterPolynomial s tag₁ * parameterPolynomial t tag₂) =
      aeval (Sum.elim
        (fun k : ℕ+ => rationalOperation k (parameterPolynomial s tag₁))
        (fun k : ℕ+ => rationalOperation k (parameterPolynomial t tag₂)))
        (productPolynomial n) := by
  apply eq_of_map_eval_nat
  intro a
  rw [map_eval_rationalOperation, map_mul,
    map_int_aeval_sum (map (eval (fun i => (a i : ℚ))))]
  simp only [map_eval_rationalOperation, map_parameterPolynomial]
  exact rationalOperation_mul_natSum s t (a ∘ tag₁) (a ∘ tag₂) n

/-- Iteration identity with independent polynomial coefficient parameters. -/
theorem rationalOperation_iterate_parameter (s : Finset (σ →₀ ℕ))
    (tag : (σ →₀ ℕ) → ι) (n m : ℕ) :
    rationalOperation n (rationalOperation m (parameterPolynomial s tag)) =
      aeval (fun k : ℕ+ => rationalOperation k (parameterPolynomial s tag))
        (iterationPolynomial n m) := by
  apply eq_of_map_eval_nat
  intro a
  rw [map_eval_rationalOperation, map_eval_rationalOperation,
    map_int_aeval (map (eval (fun i => (a i : ℚ))))]
  simp only [map_eval_rationalOperation, map_parameterPolynomial]
  exact rationalOperation_iterate_natSum s (a ∘ tag) n m

/-- The product identity holds for all rational coefficients by coefficient-parameter density. -/
theorem rationalOperation_mul (f g : MvPolynomial σ ℚ) (n : ℕ) :
    rationalOperation n (f * g) =
      aeval (Sum.elim (fun k : ℕ+ => rationalOperation k f)
        (fun k : ℕ+ => rationalOperation k g)) (productPolynomial n) := by
  let a : (σ →₀ ℕ) ⊕ (σ →₀ ℕ) → ℚ := Sum.elim f.coeff g.coeff
  have h := congrArg (map (eval a)) (rationalOperation_mul_parameter f.support g.support
    (Sum.inl : (σ →₀ ℕ) → (σ →₀ ℕ) ⊕ (σ →₀ ℕ)) Sum.inr n)
  rw [map_eval_rationalOperation, map_mul, map_int_aeval_sum (map (eval a))] at h
  simp only [map_eval_rationalOperation, map_parameterPolynomial, a,
    Sum.elim_inl, Sum.elim_inr, support_sum_monomial_coeff] at h
  exact h

/-- The iteration identity holds for all rational coefficients, including signed coefficients. -/
theorem rationalOperation_iterate (f : MvPolynomial σ ℚ) (n m : ℕ) :
    rationalOperation n (rationalOperation m f) =
      aeval (fun k : ℕ+ => rationalOperation k f) (iterationPolynomial n m) := by
  have h := congrArg (map (eval f.coeff))
    (rationalOperation_iterate_parameter f.support id n m)
  rw [map_eval_rationalOperation, map_eval_rationalOperation,
    map_int_aeval (map (eval f.coeff))] at h
  simp only [map_eval_rationalOperation, map_parameterPolynomial, id_eq,
    support_sum_monomial_coeff] at h
  exact h

end LambdaRing.Polynomial
