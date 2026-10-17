import SymmetricFunctions.Plethysm.Integral
import SymmetricFunctions.Hopf.Primitive
import LambdaRing.Polynomial.Newton

/-!
# Integral Adams operations and finite alphabet expansion

The map initially substitutes p_k into the outer symmetric function. Its finite
realization raises actual alphabet variables to their kth powers. This is not
the polynomial presentation's operation on elementary-generator variables.
-/

noncomputable section

namespace LambdaRing.Polynomial

/-- Raising every polynomial variable to a fixed power preserves exterior powers. -/
def expandHom (k : ℕ) (σ : Type*) : LambdaRingHom (MvPolynomial σ ℤ) (MvPolynomial σ ℤ) :=
  monomialHom (MvPolynomial.expand k).toRingHom (by
    intro i
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.expand_X]
    exact (isLineMonomial_X i).pow k)

@[simp] theorem expandHom_apply (k : ℕ) {σ : Type*} (f : MvPolynomial σ ℤ) :
    expandHom k σ f = MvPolynomial.expand k f := rfl

end LambdaRing.Polynomial

namespace SymmetricFunction

/-- The positive Adams map, initially expressed as f[p_k]. -/
def adams (k : ℕ+) : LambdaRingHom (SymmetricFunction ℤ) (SymmetricFunction ℤ) :=
  lambdaEval (p k)

theorem adams_apply (k : ℕ+) (f : SymmetricFunction ℤ) : adams k f = plethysm f (p k) := rfl

@[simp] theorem adams_e_one (k : ℕ+) : adams k (e 1) = p k := lambdaEval_e_one _

/-- Adams operations raise finite alphabet variables, not elementary-generator variables. -/
theorem rhoPolynomial_adams (N : ℕ) (k : ℕ+) (f : SymmetricFunction ℤ) :
    rhoPolynomial N (adams k f) = MvPolynomial.expand k (rhoPolynomial N f) := by
  have he : (rhoLambdaHom N).comp (adams k) =
      (LambdaRing.Polynomial.expandHom k (Fin N)).comp (rhoLambdaHom N) := by
    apply lambdaHom_ext
    change rhoPolynomial N (lambdaEval (p k) (e 1)) =
      MvPolynomial.expand k (rhoPolynomial N (e 1))
    rw [lambdaEval_e_one]
    simp [rhoPolynomial_apply, rho_p, rho_e, MvPolynomial.psum, MvPolynomial.esymm_one]
  exact DFunLike.congr_fun he f

/-- Power-sum indices multiply under positive Adams operations, integrally. -/
@[simp] theorem adams_p (k n : ℕ+) : adams k (p n) = p (k * n) := by
  apply eq_of_rhoPolynomial_eq
  intro N
  rw [rhoPolynomial_adams]
  simp [rhoPolynomial_apply, rho_p, MvPolynomial.psum, pow_mul]

@[simp] theorem adams_one : adams 1 = LambdaRingHom.id (SymmetricFunction ℤ) := by
  apply lambdaHom_ext
  simp [adams, p_one]

/-- Composition multiplies positive Adams indices. -/
theorem adams_comp (k n : ℕ+) : (adams k).comp (adams n) = adams (k * n) := by
  apply lambdaHom_ext
  simp only [LambdaRingHom.comp_apply]
  change adams k (lambdaEval (p n) (e 1)) = lambdaEval (p (k * n)) (e 1)
  rw [lambdaEval_e_one, lambdaEval_e_one, adams_p]

theorem adams_adams (k n : ℕ+) (f : SymmetricFunction ℤ) :
    adams k (adams n f) = adams (k * n) f :=
  DFunLike.congr_fun (adams_comp k n) f

@[simp] theorem plethysm_p_p (k n : ℕ+) : plethysm (p k) (p n) = p (k * n) := by
  rw [← adams_apply, adams_p, mul_comm]

variable {A : Type*} [CommRing A]
private theorem eval_p_eq_of_newton (φ : SymmetricFunction ℤ →+* A) (q : ℕ+ → A)
    (hq : ∀ n : ℕ, (∑ ij ∈ Finset.antidiagonal n,
      (-1 : ℤ)^ij.1 • (φ (e ij.1) * q (Nat.succPNat ij.2))) =
        ((-1 : ℤ)^(n+2) * (n+1)) • φ (e (n+1))) (k : ℕ+) : φ (p k) = q k := by
  induction k using PNat.strongInductionOn with
  | _ k ih =>
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt k.pos)
    have hk : k = Nat.succPNat n := PNat.coe_injective hn
    subst k
    let F : ℕ × ℕ → A := fun ij => (-1 : ℤ)^ij.1 • (φ (e ij.1) * φ (p (Nat.succPNat ij.2)))
    let G : ℕ × ℕ → A := fun ij => (-1 : ℤ)^ij.1 • (φ (e ij.1) * q (Nat.succPNat ij.2))
    have hs := congrArg φ (newton_convolution (R := ℤ) n)
    have hcast (z : ℤ) : algebraMap ℤ (SymmetricFunction ℤ) z = (z : SymmetricFunction ℤ) :=
      map_intCast (algebraMap ℤ (SymmetricFunction ℤ)) z
    have hcastA (z : ℤ) : algebraMap ℤ A z = (z : A) :=
      map_intCast (algebraMap ℤ A) z
    have hs'  : (∑ ij ∈ Finset.antidiagonal n, F ij) =
        ((-1 : ℤ)^(n+2) * (n+1)) • φ (e (n+1)) := by
      simpa only [F, Algebra.smul_def, hcast, map_sum, map_mul, map_intCast,
        zsmul_eq_mul, hcastA, Int.cast_mul, Nat.cast_add, Nat.cast_one] using hs
    have he : (∑ ij ∈ Finset.antidiagonal n, F ij) = ∑ ij ∈ Finset.antidiagonal n, G ij :=
      hs'.trans (hq n).symm
    have hrest : (∑ ij ∈ (Finset.antidiagonal n).erase (0,n), F ij) =
        ∑ ij ∈ (Finset.antidiagonal n).erase (0,n), G ij := by
      apply Finset.sum_congr rfl
      intro ij hij
      have hm := Finset.mem_erase.mp hij
      have hp := Finset.mem_antidiagonal.mp hm.2
      have hj : ij.2 < n := by
        have hn : ij ≠ (0,n) := hm.1
        by_contra h
        apply hn
        apply Prod.ext <;> omega
      dsimp [F, G]
      rw [ih (Nat.succPNat ij.2) (by simpa using hj)]
    rw [← Finset.add_sum_erase _ F (by simp : (0,n) ∈ Finset.antidiagonal n),
      ← Finset.add_sum_erase _ G (by simp : (0,n) ∈ Finset.antidiagonal n), hrest] at he
    simpa [F, G] using add_right_cancel he
end SymmetricFunction
namespace SymmetricFunction
open LambdaRing.Polynomial MvPolynomial

/-- The universal Adams polynomial raises every actual alphabet variable to its kth power. -/
theorem lambdaEval_p_polynomial {σ : Type*} (f : MvPolynomial σ ℤ) (k : ℕ+) :
    lambdaEval f (p k) = expand k f := by
  apply eval_p_eq_of_newton (lambdaEval f).toRingHom (fun i => expand i f)
  intro n
  simp only [LambdaRingHom.coe_toRingHom, lambdaEval_e, lambda_eq_operation,
    Nat.succPNat_coe, Nat.succ_eq_add_one]
  have hsign (ij : ℕ × ℕ) (hij : ij ∈ Finset.antidiagonal n) :
      (-1 : ℤ)^n * (-1 : ℤ)^ij.2 = (-1 : ℤ)^ij.1 := by
    rw [← Finset.mem_antidiagonal.mp hij, pow_add, mul_assoc, ← mul_pow]
    simp
  calc
    _ = (-1 : ℤ)^n • (∑ ij ∈ Finset.antidiagonal n,
        (-1 : ℤ)^ij.1 • (operation ij.2 f * expand (ij.1+1) f)) := by
      rw [Finset.smul_sum]
      conv_rhs => rw [← Finset.Nat.sum_antidiagonal_swap]
      apply Finset.sum_congr rfl
      intro ij hij
      simp only [Prod.swap, smul_smul, hsign ij hij]
    _ = (-1 : ℤ)^n • ((n+1 : ℤ) • operation (n+1) f) := by rw [operation_newton]
    _ = _ := by rw [smul_smul, pow_add]; simp

/-- Left plethysm by a power sum is the integral Adams operation. -/
@[simp] theorem plethysm_p (k : ℕ+) (f : SymmetricFunction ℤ) :
    plethysm (p k) f = adams k f := by
  apply eq_of_rhoPolynomial_eq
  intro N
  rw [rhoPolynomial_adams]
  change rhoLambdaHom N (lambdaEval f (p k)) = _
  have h := DFunLike.congr_fun (lambdaEval_natural (rhoLambdaHom N) f) (p k)
  change rhoLambdaHom N (lambdaEval f (p k)) = lambdaEval (rhoLambdaHom N f) (p k) at h
  rw [h, lambdaEval_p_polynomial]
  rfl

/-- In particular virtual negation negates each power sum, irrespective of parity. -/
@[simp] theorem plethysm_p_neg (k : ℕ+) (f : SymmetricFunction ℤ) :
    plethysm (p k) (-f) = -plethysm (p k) f := by
  simp only [plethysm_p, map_neg]

end SymmetricFunction
