import LambdaRing.Polynomial.Naturality
import LambdaRing.UniversalPolynomials.Generating

/-! # Special identities for finite sums of monomial line elements -/

noncomputable section

namespace LambdaRing.Polynomial

open MvPolynomial UniversalPolynomial

variable {σ ι κ : Type*}

theorem totalUnit_sum (s : Finset ι) (x : ι → MvPolynomial σ ℤ) :
    totalUnit (∑ i ∈ s, x i) = ∏ i ∈ s, totalUnit (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, totalUnit_add, ih]

/-- Exterior powers of a finite sum of line monomials are elementary values. -/
theorem operation_sum_lines [Fintype ι] (x : ι → MvPolynomial σ ℤ)
    (hx : ∀ i, IsLineMonomial (x i)) (n : ℕ) :
    operation n (∑ i, x i) = elementaryValue x n := by
  classical
  rw [operation, totalUnit_sum]
  simp_rw [(hx _).totalUnit]
  rw [Units.coe_prod]
  exact coeff_elementarySeries x n

/-- Positive line sums satisfy the universal product identity. -/
theorem operation_mul_sum_lines [Fintype ι] [Fintype κ]
    (x : ι → MvPolynomial σ ℤ) (y : κ → MvPolynomial σ ℤ)
    (hx : ∀ i, IsLineMonomial (x i)) (hy : ∀ j, IsLineMonomial (y j)) (n : ℕ) :
    operation n ((∑ i, x i) * ∑ j, y j) =
      aeval (Sum.elim (fun k : ℕ+ => operation k (∑ i, x i))
        (fun k : ℕ+ => operation k (∑ j, y j))) (productPolynomial n) := by
  classical
  have he : (∑ i, x i) * (∑ j, y j) = ∑ ij : ι × κ, x ij.1 * y ij.2 := by
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  rw [he, operation_sum_lines (fun ij : ι × κ => x ij.1 * y ij.2)
    (fun ij => (hx ij.1).mul (hy ij.2)) n]
  simp_rw [operation_sum_lines x hx, operation_sum_lines y hy]
  exact (productPolynomial_eval x y n).symm

/-- Squarefree elementary values are sums indexed by the actual subset alphabet. -/
theorem elementaryValue_eq_sum_squarefree [Fintype ι]
    (x : ι → MvPolynomial σ ℤ) (m : ℕ) :
    elementaryValue x m = ∑ s : SquarefreeIndex ι m, squarefreeValue x s := by
  classical
  exact (Finset.sum_attach (Finset.univ.powersetCard m) (fun t => ∏ i ∈ t, x i)).symm

/-- Positive line sums satisfy the universal iteration identity, also at m=0. -/
theorem operation_iterate_sum_lines [Fintype ι] (x : ι → MvPolynomial σ ℤ)
    (hx : ∀ i, IsLineMonomial (x i)) (n m : ℕ) :
    operation n (operation m (∑ i, x i)) =
      aeval (fun k : ℕ+ => operation k (∑ i, x i)) (iterationPolynomial n m) := by
  classical
  rw [operation_sum_lines x hx, elementaryValue_eq_sum_squarefree]
  rw [operation_sum_lines (squarefreeValue x (m := m))
    (fun s => isLineMonomial_prod s.val x (fun i _ => hx i)) n]
  simp_rw [operation_sum_lines x hx]
  exact (iterationPolynomial_eval x n m).symm

/-- A finite alphabet repeating each monomial according to a natural multiplicity. -/
abbrev MultiplicityAlphabet (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ℕ) :=
  Σ m : s, Fin (c m.val)

/-- The line value of an entry in a multiplicity alphabet. -/
def multiplicityLine (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ℕ)
    (i : MultiplicityAlphabet s c) : MvPolynomial σ ℤ := monomial i.1.val 1

theorem multiplicityLine_isLine (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ℕ)
    (i : MultiplicityAlphabet s c) : IsLineMonomial (multiplicityLine s c i) :=
  Or.inr ⟨i.1.val, rfl⟩

/-- Repetition realizes every finite polynomial sum with natural coefficients. -/
theorem sum_multiplicityLine (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ℕ) :
    (∑ i : MultiplicityAlphabet s c, multiplicityLine s c i) =
      ∑ m ∈ s, monomial m (c m : ℤ) := by
  classical
  rw [Fintype.sum_sigma]
  simp only [multiplicityLine, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℤ, ← map_smul, smul_eq_mul, mul_one]
  exact Finset.sum_attach s (fun m => monomial m (c m : ℤ))

/-- Product identity for arbitrary finite natural-coefficient polynomial sums. -/
theorem operation_mul_natSum (s t : Finset (σ →₀ ℕ))
    (a b : (σ →₀ ℕ) → ℕ) (n : ℕ) :
    operation n ((∑ m ∈ s, monomial m (a m : ℤ)) * ∑ m ∈ t, monomial m (b m : ℤ)) =
      aeval (Sum.elim
        (fun k : ℕ+ => operation k (∑ m ∈ s, monomial m (a m : ℤ)))
        (fun k : ℕ+ => operation k (∑ m ∈ t, monomial m (b m : ℤ))))
        (productPolynomial n) := by
  classical
  simpa only [sum_multiplicityLine] using operation_mul_sum_lines
    (multiplicityLine s a) (multiplicityLine t b)
    (multiplicityLine_isLine s a) (multiplicityLine_isLine t b) n

/-- Iteration identity for arbitrary finite natural-coefficient polynomial sums. -/
theorem operation_iterate_natSum (s : Finset (σ →₀ ℕ)) (a : (σ →₀ ℕ) → ℕ) (n m : ℕ) :
    operation n (operation m (∑ d ∈ s, monomial d (a d : ℤ))) =
      aeval (fun k : ℕ+ => operation k (∑ d ∈ s, monomial d (a d : ℤ)))
        (iterationPolynomial n m) := by
  classical
  simpa only [sum_multiplicityLine] using operation_iterate_sum_lines
    (multiplicityLine s a) (multiplicityLine_isLine s a) n m

end LambdaRing.Polynomial
