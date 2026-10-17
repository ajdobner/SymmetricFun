import SymmetricFunctions.Complete
import SymmetricFunctions.Specialization
import SymmetricFunctions.Finite.Generating
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-! # Positive power sums and finite compatibility -/

namespace SymmetricFunction

noncomputable section

open Finset

variable {R : Type*} [CommRing R]

/-- The recursively defined complete functions specialize to Mathlib's complete polynomials. -/
theorem rho_h (N n : ℕ) :
    (rho R N (h n) : MvPolynomial (Fin N) R) = MvPolynomial.hsymm (Fin N) R n := by
  let φ := (MvPolynomial.symmetricSubalgebra (Fin N) R).val.comp (rho R N)
  change φ (h n) = _
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [h_succ, map_sum, SymmetricFunctions.hsymm_succ]
      apply Finset.sum_congr rfl
      intro ij hij
      have hp := Finset.mem_antidiagonal.mp hij
      rw [map_smul, map_mul, ih ij.2 (by omega)]
      change (-1 : R) ^ ij.1 •
        ((rho R N (e (ij.1 + 1)) : MvPolynomial (Fin N) R) * _) = _
      rw [rho_e]
      simp [Algebra.smul_def, mul_assoc]

/-- The strictly internal terms in the positive Newton recurrence. -/
def newtonPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (antidiagonal n).filter (fun ij => 0 < ij.1 ∧ ij.1 < n)

theorem newtonPairs_spec {n : ℕ} {ij : ℕ × ℕ} (hij : ij ∈ newtonPairs n) :
    ij.1 + ij.2 = n ∧ 0 < ij.1 ∧ ij.1 < n := by
  exact ⟨Finset.mem_antidiagonal.mp (Finset.mem_filter.mp hij).1,
    (Finset.mem_filter.mp hij).2⟩

/-- The positive right index of an internal Newton term. -/
def newtonRight {n : ℕ} (ij : {ij : ℕ × ℕ // ij ∈ newtonPairs n}) : ℕ+ :=
  Nat.toPNat ij.val.2 (by have hp := newtonPairs_spec ij.property; omega)

@[simp] theorem coe_newtonRight {n : ℕ} (ij : {ij : ℕ × ℕ // ij ∈ newtonPairs n}) :
    (newtonRight ij : ℕ) = ij.val.2 := rfl

theorem newtonRight_lt {n : ℕ} (ij : {ij : ℕ × ℕ // ij ∈ newtonPairs n}) :
    (newtonRight ij : ℕ) < n := by
  have hp := newtonPairs_spec ij.property
  simp only [coe_newtonRight]
  omega

/-- Positive power sums, defined by the integral Newton recurrence. -/
def p (k : ℕ+) : SymmetricFunction R :=
  ((-1 : R)^((k : ℕ) + 1) * ((k : ℕ) : R)) • e (k : ℕ) -
    ∑ ij ∈ (newtonPairs k).attach,
      (-1 : R)^ij.val.1 • (e ij.val.1 * p (newtonRight ij))
termination_by (k : ℕ)
decreasing_by exact newtonRight_lt ij

/-- The division-free Newton recurrence; every recursive index is strictly positive. -/
theorem p_rec (k : ℕ+) :
    p (R := R) k = ((-1 : R)^((k : ℕ) + 1) * ((k : ℕ) : R)) • e (k : ℕ) -
      ∑ ij ∈ (newtonPairs k).attach,
        (-1 : R)^ij.val.1 • (e ij.val.1 * p (newtonRight ij)) := by
  rw [p]

@[simp] theorem isHomogeneous_p (k : ℕ+) : IsHomogeneous (p (R := R) k) k := by
  induction k using PNat.strongInductionOn with
  | _ k ih =>
    rw [p_rec]
    apply (homogeneousSubmodule R k).sub_mem
    · exact (isHomogeneous_e k).smul _
    · apply (homogeneousSubmodule R k).sum_mem
      intro ij _
      have hp := newtonPairs_spec ij.property
      have hg := (isHomogeneous_e (R := R) ij.val.1).mul
        (ih (newtonRight ij) (newtonRight_lt ij))
      change IsHomogeneous _ (k : ℕ)
      simpa only [coe_newtonRight, hp.1] using hg.smul ((-1 : R)^ij.val.1)

/-- Power sums specialize to Mathlib's finite power-sum polynomials. -/
theorem rho_p (N : ℕ) (k : ℕ+) :
    (rho R N (p k) : MvPolynomial (Fin N) R) = MvPolynomial.psum (Fin N) R k := by
  let φ := (MvPolynomial.symmetricSubalgebra (Fin N) R).val.comp (rho R N)
  change φ (p k) = _
  induction k using PNat.strongInductionOn with
  | _ k ih =>
    rw [p_rec, map_sub, map_smul, map_sum,
      MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin N) R k k.pos]
    congr 1
    · change _ • (rho R N (e (k : ℕ)) : MvPolynomial (Fin N) R) = _
      rw [rho_e]
      simp [Algebra.smul_def, mul_assoc]
    · have ht : ∀ ij ∈ (newtonPairs (k : ℕ)).attach,
          φ ((-1 : R)^ij.val.1 • (e ij.val.1 * p (newtonRight ij))) =
            (-1 : MvPolynomial (Fin N) R)^ij.val.1 *
              MvPolynomial.esymm (Fin N) R ij.val.1 *
                MvPolynomial.psum (Fin N) R ij.val.2 := by
        intro ij _
        rw [map_smul, map_mul, ih (newtonRight ij) (newtonRight_lt ij)]
        change _ • ((rho R N (e ij.val.1) : MvPolynomial (Fin N) R) * _) = _
        rw [rho_e]
        simp [Algebra.smul_def, mul_assoc]
      rw [Finset.sum_congr rfl ht]
      exact Finset.sum_attach _ (fun ij : ℕ × ℕ =>
        (-1 : MvPolynomial (Fin N) R)^ij.1 * MvPolynomial.esymm (Fin N) R ij.1 *
          MvPolynomial.psum (Fin N) R ij.2)

@[simp] theorem p_one : p (R := R) 1 = e 1 := by
  have he : (newtonPairs 1).attach = ∅ := by decide
  rw [p_rec]
  simp [he]

theorem p_two : p (R := R) 2 = e 1 ^ 2 - 2 * e 2 := by
  let j : {ij : ℕ × ℕ // ij ∈ newtonPairs 2} := ⟨(1, 1), by decide⟩
  have he : (newtonPairs 2).attach = {j} := by decide
  rw [p_rec]
  simp [he, j, newtonRight, Nat.toPNat, Algebra.smul_def, map_ofNat, pow_succ,
    sub_eq_add_neg, add_comm, mul_comm]

@[simp] theorem rho_h_empty (n : ℕ+) : rho R 0 (h n) = 0 := by
  rcases n with ⟨n, hn⟩
  cases n with
  | zero => omega
  | succ n =>
    apply Subtype.ext
    rw [rho_h]
    change (∑ s : Sym (Fin 0) (n + 1),
      (s.val.map MvPolynomial.X).prod : MvPolynomial (Fin 0) R) = 0
    apply Finset.sum_eq_zero
    intro s _
    exact isEmptyElim s

@[simp] theorem rho_p_empty (n : ℕ+) : rho R 0 (p n) = 0 := by
  apply Subtype.ext
  rw [rho_p]
  simp [MvPolynomial.psum]

section Examples

attribute [local irreducible] SymmetricFunction

example : p (R := R) 2 + 2 * e 2 = e 1 ^ 2 := by rw [p_two]; ring

example : IsHomogeneous (p (R := R) 2) 2 := isHomogeneous_p 2

end Examples

end

end SymmetricFunction
