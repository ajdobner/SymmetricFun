import LambdaRing.Polynomial.Newton

/-! # Auxiliary rational Newton polynomials

These operations are auxiliary finite polynomial expressions. Integral operations
remain the signed unit products, and equality with them is proved below.
-/

noncomputable section

namespace LambdaRing.Polynomial

open MvPolynomial

variable {σ R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]

/-- The divided Newton recurrence over a rational coefficient algebra. -/
def rationalOperation (n : ℕ) (f : MvPolynomial σ R) : MvPolynomial σ R :=
  match n with
  | 0 => 1
  | n+1 => (n+1 : ℚ)⁻¹ • ∑ ij ∈ (Finset.antidiagonal n).attach,
      (-1 : ℤ)^ij.val.1 • (rationalOperation ij.val.2 f * expand (ij.val.1+1) f)
termination_by n
decreasing_by
  have h := Finset.mem_antidiagonal.mp ij.property
  omega

@[simp] theorem rationalOperation_zero (f : MvPolynomial σ R) : rationalOperation 0 f = 1 := by
  rw [rationalOperation]

theorem rationalOperation_succ (n : ℕ) (f : MvPolynomial σ R) :
    rationalOperation (n+1) f = (n+1 : ℚ)⁻¹ • ∑ ij ∈ Finset.antidiagonal n,
      (-1 : ℤ)^ij.1 • (rationalOperation ij.2 f * expand (ij.1+1) f) := by
  rw [rationalOperation]
  congr 1
  exact Finset.sum_attach (Finset.antidiagonal n) (fun ij : ℕ × ℕ =>
    (-1 : ℤ)^ij.1 • (rationalOperation ij.2 f * expand (ij.1+1) f))

/-- The recursive auxiliary operations commute with rational coefficient algebra maps. -/
theorem rationalOperation_map (φ : R →ₐ[ℚ] S) (n : ℕ) (f : MvPolynomial σ R) :
    mapAlgHom φ (rationalOperation n f) = rationalOperation n (mapAlgHom φ f) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [rationalOperation_succ, map_smul, map_sum, rationalOperation_succ]
      congr 1
      apply Finset.sum_congr rfl
      intro ij hij
      rw [map_zsmul, map_mul, ih ij.2 (by have h := Finset.mem_antidiagonal.mp hij; omega)]
      simp only [mapAlgHom_apply, map_expand]

/-- The constructed integral operations satisfy the auxiliary recurrence after coefficient map.
No assertion of specialness or Adams characterization is used. -/
theorem map_operation_eq_rationalOperation (n : ℕ) (f : MvPolynomial σ ℤ) :
    map (Int.castRingHom R) (operation n f) =
      rationalOperation n (map (Int.castRingHom R) f) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      have hn : (n+1 : ℚ) ≠ 0 := by positivity
      have hc := congrArg (map (Int.castRingHom R)) (operation_newton f n)
      simp only [map_zsmul, map_sum, map_mul, map_expand] at hc
      have hsmul : (n+1 : ℚ) • map (Int.castRingHom R) (operation (n+1) f) =
          ∑ ij ∈ Finset.antidiagonal n, (-1 : ℤ)^ij.1 •
            (map (Int.castRingHom R) (operation ij.2 f) *
              expand (ij.1+1) (map (Int.castRingHom R) f)) := by
        convert hc using 1; simp [← Int.cast_smul_eq_zsmul ℚ]
      calc
        _ = (n+1 : ℚ)⁻¹ • ((n+1 : ℚ) • map (Int.castRingHom R) (operation (n+1) f)) :=
          (inv_smul_smul₀ hn _).symm
        _ = _ := by
          rw [hsmul, rationalOperation_succ]
          congr 1
          apply Finset.sum_congr rfl
          intro ij hij
          rw [ih ij.2 (by have h := Finset.mem_antidiagonal.mp hij; omega)]

end LambdaRing.Polynomial
