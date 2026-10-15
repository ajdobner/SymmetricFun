import SymmetricFunctions.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# Finite alphabets and zero-last-variable transitions

The specialization `rho` takes values in the symmetric subalgebra. Its transition
map is proved to be literal substitution of zero for the last variable. No degree
bound or injectivity claim is part of this construction.
-/

namespace SymmetricFunction

noncomputable section

open MvPolynomial

section Semiring

variable (R : Type*) [CommSemiring R]

/-- Specialization to the alphabet indexed by `Fin N`. -/
def rho (N : ℕ) : SymmetricFunction R →ₐ[R] symmetricSubalgebra (Fin N) R :=
  eval (fun i : ℕ+ => ⟨esymm (Fin N) R i, esymm_isSymmetric _ _ _⟩)

@[simp] theorem rho_e (N k : ℕ) :
    (rho R N (e k) : MvPolynomial (Fin N) R) = esymm (Fin N) R k := by
  cases k with
  | zero => simp
  | succ k => simp [rho]

theorem rho_e_eq_zero {N k : ℕ} (h : N < k) : rho R N (e k) = 0 := by
  apply Subtype.ext
  rw [rho_e, esymm_eq_multiset_esymm]
  exact Multiset.esymm_of_card_lt (by simpa using h)

/-- Substitute zero for the last variable and retain the first `N` variables. -/
def zeroLast (N : ℕ) :
    MvPolynomial (Fin (N + 1)) R →ₐ[R] MvPolynomial (Fin N) R :=
  aeval (Fin.lastCases 0 X)

@[simp] theorem zeroLast_X_last (N : ℕ) : zeroLast R N (X (Fin.last N)) = 0 := by
  simp [zeroLast]

@[simp] theorem zeroLast_X_castSucc (N : ℕ) (i : Fin N) :
    zeroLast R N (X i.castSucc) = X i := by
  simp [zeroLast]

private lemma esymm_zero_cons {A : Type*} [CommSemiring A] (s : Multiset A) (k : ℕ) :
    (0 ::ₘ s).esymm k = s.esymm k := by
  cases k with
  | zero => simp
  | succ k => simp [Multiset.esymm, Multiset.map_map]

@[simp] theorem zeroLast_esymm (N k : ℕ) :
    zeroLast R N (esymm (Fin (N + 1)) R k) = esymm (Fin N) R k := by
  rw [zeroLast, aeval_esymm_eq_multiset_esymm, esymm_eq_multiset_esymm]
  rw [Fin.univ_castSuccEmb]
  simp only [Finset.cons_val, Finset.map_val, Multiset.map_cons, Multiset.map_map,
    Function.comp_def, Fin.lastCases_last, Fin.coe_castSuccEmb, Fin.lastCases_castSucc]
  exact esymm_zero_cons _ _

/-- The empty alphabet evaluates every positive elementary generator at zero. -/
theorem rho_zero (f : SymmetricFunction R) :
    (rho R 0 f : MvPolynomial (Fin 0) R) = C (eval (fun _ : ℕ+ => (0 : R)) f) := by
  have h : (symmetricSubalgebra (Fin 0) R).val.comp (rho R 0) =
      (Algebra.ofId R (MvPolynomial (Fin 0) R)).comp (eval (fun _ : ℕ+ => (0 : R))) := by
    apply algHom_ext
    intro i
    change (rho R 0 (e (i : ℕ)) : MvPolynomial (Fin 0) R) = _
    rw [rho_e_eq_zero R i.pos]
    simp
  exact DFunLike.congr_fun h f

end Semiring

section Ring

variable {R : Type*} [CommRing R]

/-- Restriction of zero-last-variable substitution to symmetric polynomials. -/
def transition (N : ℕ) :
    symmetricSubalgebra (Fin (N + 1)) R →ₐ[R] symmetricSubalgebra (Fin N) R :=
  (esymmAlgHom (Fin N) R (N + 1)).comp
    (esymmAlgEquiv (Fin (N + 1)) R (Fintype.card_fin _)).symm.toAlgHom

theorem coe_transition (N : ℕ) (f : symmetricSubalgebra (Fin (N + 1)) R) :
    (transition N f : MvPolynomial (Fin N) R) = zeroLast R N f := by
  obtain ⟨p, rfl⟩ := (esymmAlgEquiv (Fin (N + 1)) R (Fintype.card_fin _)).surjective f
  have h : (symmetricSubalgebra (Fin N) R).val.comp (esymmAlgHom (Fin N) R (N + 1)) =
      (zeroLast R N).comp
        ((symmetricSubalgebra (Fin (N + 1)) R).val.comp (esymmAlgHom (Fin (N + 1)) R (N + 1))) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [esymmAlgHom]
  change ((esymmAlgHom (Fin N) R (N + 1))
    ((esymmAlgEquiv (Fin (N + 1)) R (Fintype.card_fin _)).symm
      ((esymmAlgEquiv (Fin (N + 1)) R (Fintype.card_fin _)) p)) :
        MvPolynomial (Fin N) R) = _
  rw [AlgEquiv.symm_apply_apply]
  exact DFunLike.congr_fun h p

@[simp] theorem transition_esymm (N k : ℕ) :
    transition (R := R) N ⟨esymm (Fin (N + 1)) R k, esymm_isSymmetric _ _ _⟩ =
      ⟨esymm (Fin N) R k, esymm_isSymmetric _ _ _⟩ := by
  apply Subtype.ext
  simp [coe_transition]

/-- Compatibility as algebra maps, hence on every symmetric function. -/
theorem transition_comp_rho (N : ℕ) :
    (transition (R := R) N).comp (rho R (N + 1)) = rho R N := by
  apply algHom_ext
  intro i
  apply Subtype.ext
  simp [coe_transition, rho_e]

@[simp] theorem transition_rho (N : ℕ) (f : SymmetricFunction R) :
    transition N (rho R (N + 1) f) = rho R N f :=
  DFunLike.congr_fun (transition_comp_rho N) f

theorem zeroLast_rho (N : ℕ) (f : SymmetricFunction R) :
    zeroLast R N (rho R (N + 1) f) = rho R N f := by
  rw [← coe_transition, transition_rho]

end Ring

section Examples

variable (R : Type*) [CommSemiring R]

attribute [local irreducible] SymmetricFunction

example (f : SymmetricFunction R) :
    (rho R 0 f : MvPolynomial (Fin 0) R) = C (eval (fun _ : ℕ+ => (0 : R)) f) :=
  rho_zero R f

example : rho R 1 (e 2 + e 0) = 1 := by
  rw [map_add, rho_e_eq_zero R (by decide : 1 < 2)]
  simp

end Examples

end

end SymmetricFunction
