import LambdaRing.UniversalPolynomials.ProductDegree
import Mathlib.Algebra.Order.Monoid.Prod

/-! # Stable product polynomials in two positive elementary alphabets -/

namespace LambdaRing.UniversalPolynomial

noncomputable section

open MvPolynomial SymmetricFunction

/-- Flatten the stable first alphabet and its second-alphabet polynomial coefficients. -/
def productPolynomialOver (R : Type*) [CommRing R] (n : ℕ) : MvPolynomial (ℕ+ ⊕ ℕ+) R :=
  (sumAlgEquiv R ℕ+ ℕ+).symm
    (polynomialEquiv (MvPolynomial ℕ+ R) (productFunction R n))

/-- Any first-alphabet size at least n yields the same polynomial in positive generators. -/
theorem productPolynomialOver_eq_presentation (R : Type*) [CommRing R]
    (N n : ℕ) (hN : n ≤ N) :
    productPolynomialOver R n =
      rename (Sum.map (fun i : Fin N => Nat.succPNat i.val) id) (productPresentation R N n) := by
  have hp (q : MvPolynomial (Fin N) (MvPolynomial ℕ+ R)) :
      polynomialEquiv (MvPolynomial ℕ+ R) (finiteLift (MvPolynomial ℕ+ R) N q) =
        rename (fun i : Fin N => Nat.succPNat i.val) q := by
    have he := MvPolynomial.comp_aeval_apply
      (fun i : Fin N => e (R := MvPolynomial ℕ+ R) (i.val + 1))
      (polynomialEquiv (MvPolynomial ℕ+ R)).toAlgHom q
    have hx (i : Fin N) : polynomialEquiv (MvPolynomial ℕ+ R) (e (i.val + 1)) =
        X (Nat.succPNat i.val) := polynomialEquiv_e (Nat.succPNat i.val)
    simp only [AlgEquiv.coe_toAlgHom, hx] at he
    rw [rename_eq_aeval]
    exact he
  unfold productPolynomialOver
  rw [productFunction_eq_lift R N n hN]
  simp only [liftSymmetric, AlgHom.comp_apply]
  rw [hp]
  apply (sumAlgEquiv R ℕ+ ℕ+).injective
  rw [AlgEquiv.apply_symm_apply, sumAlgEquiv_rename_left]
  simp only [productPresentation, AlgEquiv.apply_symm_apply]
  rfl

/-- The product polynomial is homogeneous of degree n in each weighted elementary block. -/
theorem productPolynomialOver_bidegree (R : Type*) [CommRing R] (n : ℕ) :
    (productPolynomialOver R n).IsWeightedHomogeneous elementaryBlockWeight (n, n) := by
  rw [productPolynomialOver_eq_presentation R n n le_rfl]
  apply weightedHomogeneous_rename R _ _ (productPresentation_bidegree R n n)
  intro i
  cases i <;> rfl

/-- Integral coefficients of the universal product identity. -/
def productPolynomial (n : ℕ) : MvPolynomial (ℕ+ ⊕ ℕ+) ℤ := productPolynomialOver ℤ n

theorem productPolynomial_bidegree (n : ℕ) :
    (productPolynomial n).IsWeightedHomogeneous elementaryBlockWeight (n, n) :=
  productPolynomialOver_bidegree ℤ n

/-- No left elementary generator above n occurs. -/
theorem productPolynomial_vars_left_le (n : ℕ) {i : ℕ+}
    (hi : Sum.inl i ∈ (productPolynomial n).vars) : (i : ℕ) ≤ n := by
  obtain ⟨a, ha, hai⟩ := (MvPolynomial.mem_vars_iff_mem_support (Sum.inl i)).mp hi
  have hw := Finsupp.le_weight_of_ne_zero' elementaryBlockWeight (Finsupp.mem_support_iff.mp hai)
  rw [productPolynomial_bidegree n (MvPolynomial.mem_support_iff.mp ha)] at hw
  exact hw.1

/-- No right elementary generator above n occurs. -/
theorem productPolynomial_vars_right_le (n : ℕ) {i : ℕ+}
    (hi : Sum.inr i ∈ (productPolynomial n).vars) : (i : ℕ) ≤ n := by
  obtain ⟨a, ha, hai⟩ := (MvPolynomial.mem_vars_iff_mem_support (Sum.inr i)).mp hi
  have hw := Finsupp.le_weight_of_ne_zero' elementaryBlockWeight (Finsupp.mem_support_iff.mp hai)
  rw [productPolynomial_bidegree n (MvPolynomial.mem_support_iff.mp ha)] at hw
  exact hw.2

end

end LambdaRing.UniversalPolynomial
