import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Coefficients of finite products in separate alphabet variables -/

noncomputable section
namespace SymmetricFunctions
variable {σ A : Type*} [Fintype σ] [CommRing A]

open Classical in
/-- A finite polynomial in each independent variable has independent coefficients. -/
theorem coeff_prod_separated (B : σ → ℕ) (c : σ → ℕ → A) (a : σ →₀ ℕ) :
    (∏ i : σ, ∑ r : Fin (B i + 1),
      MvPolynomial.C (c i r.val) * MvPolynomial.X i ^ r.val).coeff a =
        ∏ i : σ, if a i ≤ B i then c i (a i) else 0 := by
  classical
  rw [Fintype.prod_sum, MvPolynomial.coeff_sum]
  simp_rw [Finset.prod_mul_distrib, ← map_prod, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_prod_X_pow]
  by_cases ha : ∀ i, a i ≤ B i
  · let t : ∀ i, Fin (B i + 1) := fun i => ⟨a i, Nat.lt_succ_of_le (ha i)⟩
    rw [Finset.sum_eq_single t]
    · have he : Finsupp.indicator Finset.univ (fun i _ => (t i).val) = a := by
        ext i
        simp [t]
      simp only [he, ite_true, mul_one, t, ha]
    · intro u _ hut
      have hn : a ≠ Finsupp.indicator Finset.univ (fun i _ => (u i).val) := by
        intro he
        apply hut
        funext i
        apply Fin.ext
        have hi := DFunLike.congr_fun he i
        simpa [t] using hi.symm
      rw [ite_eq_right hn, mul_zero]
    · simp
  · obtain ⟨i, hi⟩ := not_forall.mp ha
    have hz : (∏ j : σ, if a j ≤ B j then c j (a j) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
    rw [hz]
    apply Finset.sum_eq_zero
    intro u _
    have hn : a ≠ Finsupp.indicator Finset.univ (fun j _ => (u j).val) := by
      intro he
      have hai : a i = (u i).val := by simpa using DFunLike.congr_fun he i
      exact hi (hai ▸ Nat.le_of_lt_succ (u i).isLt)
    rw [ite_eq_right hn, mul_zero]

open Classical in
/-- Coefficients of a matrix with independent column variables form a determinant. -/
theorem coeff_det_separated {N : ℕ} (B : Fin N → ℕ)
    (c : Fin N → Fin N → ℕ → A) (a : Fin N →₀ ℕ) :
    (Matrix.of (fun i j : Fin N => ∑ r : Fin (B i + 1),
      MvPolynomial.C (c i j r.val) * MvPolynomial.X j ^ r.val)).det.coeff a =
        (Matrix.of (fun i j : Fin N => if a j ≤ B i then c i j (a j) else 0)).det := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_smul, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro σ _
  exact congrArg (Equiv.Perm.sign σ • ·)
    (coeff_prod_separated (fun j => B (σ j)) (fun j r => c (σ j) j r) a)

end SymmetricFunctions
