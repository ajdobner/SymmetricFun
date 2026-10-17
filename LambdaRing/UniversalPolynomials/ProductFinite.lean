import LambdaRing.UniversalPolynomials.Generating
import SymmetricFunctions.Stable

/-! # The first-alphabet family for universal product polynomials

The coefficient ring consists of finite polynomials in the elementary generators
of the second alphabet. Formal series are used only to extract finite coefficients.
-/

namespace LambdaRing.UniversalPolynomial

noncomputable section

open Finset MvPolynomial

variable (R : Type*) [CommRing R]

/-- The second alphabet's elementary generators, with the required constant term. -/
def elementaryCoefficient (k : ℕ) : MvPolynomial ℕ+ R :=
  SymmetricFunction.polynomialEquiv R (SymmetricFunction.e k)

@[simp] theorem elementaryCoefficient_zero : elementaryCoefficient R 0 = 1 := by
  simp [elementaryCoefficient]

@[simp] theorem elementaryCoefficient_pos (k : ℕ+) : elementaryCoefficient R k = X k := by
  simp [elementaryCoefficient]

/-- One first-alphabet variable scales the elementary generating series in the second. -/
def productFactor {σ : Type*} (i : σ) : PowerSeries (MvPolynomial σ (MvPolynomial ℕ+ R)) :=
  PowerSeries.mk (fun k => C (elementaryCoefficient R k) * X i ^ k)

@[simp] theorem coeff_productFactor {σ : Type*} (i : σ) (k : ℕ) :
    PowerSeries.coeff k (productFactor R i) = C (elementaryCoefficient R k) * X i ^ k :=
  PowerSeries.coeff_mk _ _

/-- The finite product over the first alphabet. -/
def productSeries (σ : Type*) [Fintype σ] : PowerSeries (MvPolynomial σ (MvPolynomial ℕ+ R)) :=
  ∏ i : σ, productFactor R i

/-- A finite polynomial: the nth coefficient of the first-alphabet product. -/
def productFinite (σ : Type*) [Fintype σ] (n : ℕ) : MvPolynomial σ (MvPolynomial ℕ+ R) :=
  PowerSeries.coeff n (productSeries R σ)

/-- The explicit finite coefficient formula. -/
theorem productFinite_eq_sum (σ : Type*) [Fintype σ] [DecidableEq σ] (n : ℕ) :
    productFinite R σ n =
      ∑ a ∈ Finset.finsuppAntidiag (univ : Finset σ) n,
        ∏ i : σ, C (elementaryCoefficient R (a i)) * X i ^ a i := by
  simp [productFinite, productSeries, PowerSeries.coeff_prod]

/-- The first alphabet has homogeneous degree n. -/
theorem productFinite_isHomogeneous (σ : Type*) [Fintype σ] (n : ℕ) :
    (productFinite R σ n).IsHomogeneous n := by
  classical
  rw [productFinite_eq_sum]
  apply (homogeneousSubmodule σ (MvPolynomial ℕ+ R) n).sum_mem
  intro a ha
  have hd := (Finset.mem_finsuppAntidiag.mp ha).1
  have hx (i : σ) : (C (elementaryCoefficient R (a i)) * X i ^ a i).IsHomogeneous (a i) := by
    simpa using ((isHomogeneous_X (MvPolynomial ℕ+ R) i).pow (a i)).C_mul
      (elementaryCoefficient R (a i))
  have hp := IsHomogeneous.prod univ
    (fun i : σ => C (elementaryCoefficient R (a i)) * X i ^ a i) (fun i => a i)
    (fun i _ => hx i)
  rw [hd] at hp
  exact hp

/-- Renaming the first variable renames its entire factor. -/
@[simp] theorem map_productFactor {σ τ : Type*} (f : σ → τ) (i : σ) :
    PowerSeries.map (rename f).toRingHom (productFactor R i) = productFactor R (f i) := by
  ext n
  simp

/-- Permuting first-alphabet variables preserves the coefficient polynomial. -/
theorem productFinite_isSymmetric (σ : Type*) [Fintype σ] (n : ℕ) :
    IsSymmetric (productFinite R σ n) := by
  intro e
  have hs : PowerSeries.map (rename e).toRingHom (productSeries R σ) = productSeries R σ := by
    simp only [productSeries, map_prod, map_productFactor]
    exact Equiv.prod_comp e (productFactor R)
  have hc := congrArg (PowerSeries.coeff n) hs
  exact hc

@[simp] theorem zeroLast_productFactor_castSucc (N : ℕ) (i : Fin N) :
    PowerSeries.map (SymmetricFunction.zeroLast (MvPolynomial ℕ+ R) N).toRingHom
      (productFactor R i.castSucc) = productFactor R i := by
  ext n
  simp

@[simp] theorem zeroLast_productFactor_last (N : ℕ) :
    PowerSeries.map (SymmetricFunction.zeroLast (MvPolynomial ℕ+ R) N).toRingHom
      (productFactor R (Fin.last N)) = 1 := by
  ext n
  by_cases hn : n = 0 <;> simp [hn]

/-- The first-alphabet family is compatible with zero-last-variable substitution. -/
theorem zeroLast_productFinite (N n : ℕ) :
    SymmetricFunction.zeroLast (MvPolynomial ℕ+ R) N (productFinite R (Fin (N + 1)) n) =
      productFinite R (Fin N) n := by
  have hs : PowerSeries.map (SymmetricFunction.zeroLast (MvPolynomial ℕ+ R) N).toRingHom
      (productSeries R (Fin (N + 1))) = productSeries R (Fin N) := by
    simp only [productSeries, Fin.prod_univ_castSucc, map_mul, map_prod,
      zeroLast_productFactor_castSucc, zeroLast_productFactor_last, mul_one]
  have hc := congrArg (PowerSeries.coeff n) hs
  exact hc

/-- A uniformly bounded stable family, with the second elementary alphabet as coefficients. -/
def productFamily (n : ℕ) : SymmetricFunction.BoundedStable (MvPolynomial ℕ+ R) :=
  ⟨fun N => ⟨productFinite R (Fin N) n, productFinite_isSymmetric R (Fin N) n⟩,
    (by
      intro N
      apply Subtype.ext
      exact (SymmetricFunction.coe_transition N _).trans (zeroLast_productFinite R N n)),
    n, fun N => (productFinite_isHomogeneous R (Fin N) n).totalDegree_le⟩

/-- The outer symmetric function, with second-alphabet polynomial coefficients. -/
def productFunction (n : ℕ) : SymmetricFunction (MvPolynomial ℕ+ R) :=
  (SymmetricFunction.stableEquiv (MvPolynomial ℕ+ R)).symm (productFamily R n)

@[simp] theorem rho_productFunction (N n : ℕ) :
    (SymmetricFunction.rho (MvPolynomial ℕ+ R) N (productFunction R n) :
      MvPolynomial (Fin N) (MvPolynomial ℕ+ R)) = productFinite R (Fin N) n := by
  exact congrArg Subtype.val
    (SymmetricFunction.rho_stableEquiv_symm (MvPolynomial ℕ+ R) (productFamily R n) N)

/-- Every first-alphabet size at least n gives the same outer symmetric function. -/
theorem productFunction_eq_lift (N n : ℕ) (hN : n ≤ N) :
    productFunction R n = SymmetricFunction.liftSymmetric (MvPolynomial ℕ+ R) N
      ⟨productFinite R (Fin N) n, productFinite_isSymmetric R (Fin N) n⟩ :=
  SymmetricFunction.stableEquiv_symm_eq_lift (MvPolynomial ℕ+ R) (productFamily R n)
    (fun K => (productFinite_isHomogeneous R (Fin K) n).totalDegree_le) hN

theorem productFunction_isHomogeneous (n : ℕ) :
    SymmetricFunction.IsHomogeneous (productFunction R n) n := by
  rw [productFunction_eq_lift R n n le_rfl]
  exact SymmetricFunction.isHomogeneous_liftSymmetric _ _ _ _ (productFinite_isHomogeneous R _ n)

end

end LambdaRing.UniversalPolynomial
