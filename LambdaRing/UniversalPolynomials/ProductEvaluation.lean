import LambdaRing.UniversalPolynomials.Product

/-! # Evaluation of the integral product polynomial on arbitrary finite alphabets -/

namespace LambdaRing.UniversalPolynomial

noncomputable section

open MvPolynomial SymmetricFunction

variable {σ τ A : Type*} [Fintype τ] [CommRing A]

/-- Evaluate the second elementary alphabet at the elementary values of y. -/
def secondAlphabetEval (y : τ → A) : MvPolynomial ℕ+ ℤ →+* A :=
  (MvPolynomial.aeval (fun i : ℕ+ => elementaryValue y i)).toRingHom

@[simp] theorem secondAlphabetEval_elementaryCoefficient (y : τ → A) (k : ℕ) :
    secondAlphabetEval y (elementaryCoefficient ℤ k) = elementaryValue y k := by
  cases k with
  | zero => simp
  | succ k =>
    change MvPolynomial.aeval (fun i : ℕ+ => elementaryValue y i)
      (polynomialEquiv ℤ (e (Nat.succPNat k))) = _
    rw [polynomialEquiv_e (Nat.succPNat k), aeval_X]
    rfl

/-- Evaluate first-alphabet variables and second-alphabet elementary coefficients. -/
def twoAlphabetEval (x : σ → A) (y : τ → A) : MvPolynomial σ (MvPolynomial ℕ+ ℤ) →+* A :=
  eval₂Hom (secondAlphabetEval y) x

/-- A universal factor becomes the elementary generating series of the scaled second alphabet. -/
theorem twoAlphabetEval_productFactor (x : σ → A) (y : τ → A) (i : σ) :
    PowerSeries.map (twoAlphabetEval x y) (productFactor ℤ i) =
      elementarySeries (fun j => x i * y j) := by
  ext k
  simp [twoAlphabetEval, elementaryValue_mul_left, mul_comm]

/-- The two nested products enumerate exactly the pairwise-product alphabet. -/
theorem twoAlphabetEval_productSeries [Fintype σ] (x : σ → A) (y : τ → A) :
    PowerSeries.map (twoAlphabetEval x y) (productSeries ℤ σ) =
      elementarySeries (fun ij : σ × τ => x ij.1 * y ij.2) := by
  classical
  simp only [productSeries, map_prod, twoAlphabetEval_productFactor]
  simp [elementarySeries, Fintype.prod_prod_type]

theorem twoAlphabetEval_productFinite [Fintype σ] (x : σ → A) (y : τ → A) (n : ℕ) :
    twoAlphabetEval x y (productFinite ℤ σ n) =
      elementaryValue (fun ij : σ × τ => x ij.1 * y ij.2) n := by
  have hc := congrArg (PowerSeries.coeff n) (twoAlphabetEval_productSeries x y)
  simpa only [PowerSeries.coeff_map, coeff_elementarySeries, productFinite] using hc

/-- The product polynomial identity for a standard finite first alphabet. -/
theorem productPolynomial_eval_fin (N n : ℕ) (x : Fin N → A) (y : τ → A) :
    MvPolynomial.aeval (Sum.elim (fun i : ℕ+ => elementaryValue x i)
      (fun j : ℕ+ => elementaryValue y j)) (productPolynomial n) =
        elementaryValue (fun ij : Fin N × τ => x ij.1 * y ij.2) n := by
  let q := polynomialEquiv (MvPolynomial ℕ+ ℤ) (productFunction ℤ n)
  have hs : aeval (fun i : ℕ+ => esymm (Fin N) (MvPolynomial ℕ+ ℤ) i) q =
      productFinite ℤ (Fin N) n := by
    rw [elementarySpecialization_eq_rho]
    change (rho (MvPolynomial ℕ+ ℤ) N (productFunction ℤ n) :
      MvPolynomial (Fin N) (MvPolynomial ℕ+ ℤ)) = _
    exact rho_productFunction ℤ N n
  have hc : (eval₂Hom (secondAlphabetEval y) x).comp C = secondAlphabetEval y := by
    apply RingHom.ext
    intro r
    exact eval₂Hom_C _ _ r
  have he := MvPolynomial.map_aeval
    (fun i : ℕ+ => esymm (Fin N) (MvPolynomial ℕ+ ℤ) i) (twoAlphabetEval x y) q
  simp only [MvPolynomial.algebraMap_eq, twoAlphabetEval, eval₂Hom_esymm] at he
  rw [hc] at he
  rw [productPolynomial, productPolynomialOver, aeval_sumAlgEquiv, AlgEquiv.apply_symm_apply]
  calc
    _ = twoAlphabetEval x y
        (aeval (fun i : ℕ+ => esymm (Fin N) (MvPolynomial ℕ+ ℤ) i) q) := he.symm
    _ = twoAlphabetEval x y (productFinite ℤ (Fin N) n) := congrArg (twoAlphabetEval x y) hs
    _ = _ := twoAlphabetEval_productFinite x y n

/-- Universal multiplication identity, valid in every commutative ring including torsion rings. -/
theorem productPolynomial_eval [Fintype σ] (x : σ → A) (y : τ → A) (n : ℕ) :
    MvPolynomial.aeval (Sum.elim (fun i : ℕ+ => elementaryValue x i)
      (fun j : ℕ+ => elementaryValue y j)) (productPolynomial n) =
        elementaryValue (fun ij : σ × τ => x ij.1 * y ij.2) n := by
  classical
  let e := (Fintype.equivFin σ).symm
  have he := productPolynomial_eval_fin (Fintype.card σ) n (x ∘ e) y
  simp only [elementaryValue_equiv] at he
  have ht := elementaryValue_equiv (e.prodCongr (Equiv.refl τ))
    (fun ij : σ × τ => x ij.1 * y ij.2) n
  exact he.trans ht

end

end LambdaRing.UniversalPolynomial
