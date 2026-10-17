import SymmetricFunctions.Grading
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Complete symmetric functions over arbitrary commutative rings

The finite integral recurrence is the coefficient form of `E(-u) H(u) = 1`.
It does not divide by integers and defines a finite polynomial at every index.
-/

namespace SymmetricFunction

noncomputable section

open Finset

variable {R : Type*} [CommRing R]

/-- The complete symmetric functions, defined by the integral inverse recurrence. -/
def h : ℕ → SymmetricFunction R
  | 0 => 1
  | n + 1 => ∑ ij ∈ (antidiagonal n).attach,
      (-1 : R) ^ ij.val.1 • (e (ij.val.1 + 1) * h ij.val.2)
termination_by n => n
decreasing_by
  have hp := Finset.mem_antidiagonal.mp ij.property
  omega

@[simp] theorem h_zero : h (R := R) 0 = 1 := by rw [h]

theorem h_succ (n : ℕ) :
    h (R := R) (n + 1) =
      ∑ ij ∈ antidiagonal n, (-1 : R) ^ ij.1 • (e (ij.1 + 1) * h ij.2) := by
  rw [h]
  exact Finset.sum_attach _ (fun ij : ℕ × ℕ =>
    (-1 : R) ^ ij.1 • (e (R := R) (ij.1 + 1) * h ij.2))

@[simp] theorem h_one : h (R := R) 1 = e 1 := by simp [h_succ]

theorem h_two : h (R := R) 2 = e 1 ^ 2 - e 2 := by
  simp [h_succ, Finset.Nat.sum_antidiagonal_succ, pow_two, sub_eq_add_neg]

@[simp] theorem isHomogeneous_h (n : ℕ) : IsHomogeneous (h (R := R) n) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [h_succ]
      apply (homogeneousSubmodule R (n + 1)).sum_mem
      intro ij hij
      have hp := Finset.mem_antidiagonal.mp hij
      have hj : ij.2 < n + 1 := by omega
      have hd : (ij.1 + 1) + ij.2 = n + 1 := by omega
      change IsHomogeneous _ (n + 1)
      simpa only [← hd] using ((isHomogeneous_e (R := R) (ij.1 + 1)).mul (ih ij.2 hj)).smul
        ((-1 : R)^ij.1)

/-- Coefficients of `E(-u) H(u) = 1`. -/
theorem e_h_convolution (n : ℕ) :
    ∑ ij ∈ antidiagonal n, (-1 : R) ^ ij.1 • (e (R := R) ij.1 * h ij.2) =
      if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Finset.Nat.sum_antidiagonal_succ]
    simp only [pow_zero, e_zero, one_mul, one_smul, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, ↓reduceIte]
    simp_rw [pow_succ, mul_smul, neg_one_smul, smul_neg, Finset.sum_neg_distrib]
    rw [← h_succ]
    exact add_neg_cancel _

/-- Coefficients of `H(u) E(-u) = 1`. -/
theorem h_e_convolution (n : ℕ) :
    ∑ ij ∈ antidiagonal n, (-1 : R) ^ ij.2 • (h (R := R) ij.1 * e ij.2) =
      if n = 0 then 1 else 0 := by
  rw [← e_h_convolution (R := R) n, ← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.swap, mul_comm]

/-- Coefficients of `E(u) H(-u) = 1`, the sign convention for the antipode. -/
theorem e_h_convolution_signed (n : ℕ) :
    ∑ ij ∈ antidiagonal n, (-1 : R) ^ ij.2 • (e (R := R) ij.1 * h ij.2) =
      if n = 0 then 1 else 0 := by
  have hs : ∀ ij ∈ antidiagonal n,
      (-1 : R) ^ n * (-1 : R) ^ ij.1 = (-1 : R) ^ ij.2 := by
    intro ij hij
    rw [← Finset.mem_antidiagonal.mp hij, pow_add]
    calc
      ((-1 : R) ^ ij.1 * (-1 : R) ^ ij.2) * (-1 : R) ^ ij.1 =
          ((-1 : R) ^ ij.1 * (-1 : R) ^ ij.1) * (-1 : R) ^ ij.2 := by ring
      _ = (-1 : R) ^ ij.2 := by rw [← mul_pow]; simp
  calc
    _ = (-1 : R) ^ n •
        ∑ ij ∈ antidiagonal n, (-1 : R) ^ ij.1 • (e (R := R) ij.1 * h ij.2) := by
      rw [smul_sum]
      apply Finset.sum_congr rfl
      intro ij hij
      rw [smul_smul, hs ij hij]
    _ = _ := by rw [e_h_convolution]; split_ifs with hn <;> simp [hn]

/-- Coefficients of `H(-u) E(u) = 1`. -/
theorem h_e_convolution_signed (n : ℕ) :
    ∑ ij ∈ antidiagonal n, (-1 : R) ^ ij.1 • (h (R := R) ij.1 * e ij.2) =
      if n = 0 then 1 else 0 := by
  rw [← e_h_convolution_signed (R := R) n, ← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.swap, mul_comm]

/-- The inverse recurrence, expressing elementary functions through complete ones. -/
theorem e_succ_h (n : ℕ) :
    e (R := R) (n + 1) =
      ∑ ij ∈ antidiagonal n, (-1 : R) ^ ij.1 • (h (ij.1 + 1) * e ij.2) := by
  have hc := h_e_convolution_signed (R := R) (n + 1)
  rw [Finset.Nat.sum_antidiagonal_succ] at hc
  simp only [pow_zero, h_zero, one_mul, one_smul, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ↓reduceIte] at hc
  simp_rw [pow_succ, mul_smul, neg_one_smul, smul_neg, Finset.sum_neg_distrib] at hc
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hc)

/-- The complete recurrence uniquely determines a sequence in the public algebra. -/
theorem h_unique (f : ℕ → SymmetricFunction R) (f0 : f 0 = 1)
    (fs : ∀ n, f (n + 1) =
      ∑ ij ∈ antidiagonal n, (-1 : R) ^ ij.1 • (e (ij.1 + 1) * f ij.2)) : f = h := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa using f0
    | succ n =>
      rw [fs, h_succ]
      apply Finset.sum_congr rfl
      intro ij hij
      have hp := Finset.mem_antidiagonal.mp hij
      rw [ih ij.2 (by omega)]

section Examples

attribute [local irreducible] SymmetricFunction

example : h (R := R) 2 + e 2 = e 1 ^ 2 := by rw [h_two]; ring

example : h (R := R) 3 ∈ degreeLE R 3 :=
  homogeneous_le_degreeLE le_rfl (isHomogeneous_h 3)

end Examples

end

end SymmetricFunction
