import SymmetricFunctions.Partition.YoungDiagram
import SymmetricFunctions.Basis.Complete
import SymmetricFunctions.Hopf.Coefficients
import SymmetricFunctions.PowerSum
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Schur functions by Jacobi–Trudi

Every index in the determinant is an integer: negative complete indices mean
zero, and index zero means one. The determinant uses the number of positive
rows; sufficient zero padding gives the same function over every commutative
ring. Finite specialization below is algebraic, without a tableau assertion.
-/

namespace SymmetricFunction

noncomputable section

open scoped BigOperators
open SymmetricFunctions.Partition

variable {R S : Type*} [CommRing R] [CommRing S] {d : ℕ}

/-- Complete functions at integer indices, with negative indices equal to zero. -/
def completeInt (k : ℤ) : SymmetricFunction R := if 0 ≤ k then h k.toNat else 0

@[simp] theorem completeInt_natCast (n : ℕ) : completeInt (R := R) (n : ℤ) = h n := by
  simp [completeInt]

@[simp] theorem completeInt_zero : completeInt (R := R) 0 = 1 := by
  simpa using completeInt_natCast (R := R) 0

@[simp] theorem completeInt_of_neg {k : ℤ} (hk : k < 0) : completeInt (R := R) k = 0 := by
  simp [completeInt, not_le.mpr hk]

@[simp] theorem completeInt_negSucc (n : ℕ) : completeInt (R := R) (-(n + 1 : ℤ)) = 0 :=
  completeInt_of_neg (by omega)

@[simp] theorem map_completeInt (φ : R →+* S) (k : ℤ) :
    map φ (completeInt k) = completeInt k := by
  unfold completeInt
  split_ifs <;> simp

/-- The Jacobi–Trudi matrix, with all subtractions performed in the integers. -/
def jacobiTrudiMatrix (ξ : Nat.Partition d) (L : ℕ) :
    Matrix (Fin L) (Fin L) (SymmetricFunction R) :=
  fun i j => completeInt ((rowLength ξ i : ℤ) - (i : ℤ) + (j : ℤ))

/-- The Schur function is the actual Jacobi–Trudi determinant at the row count. -/
def schur (ξ : Nat.Partition d) : SymmetricFunction R :=
  (jacobiTrudiMatrix ξ (length ξ)).det

/-- Adding a zero row appends a last row `(0,…,0,1)` to the determinant. -/
theorem det_jacobiTrudiMatrix_succ (ξ : Nat.Partition d) {L : ℕ}
    (hL : length ξ ≤ L) :
    (jacobiTrudiMatrix (R := R) ξ (L + 1)).det = (jacobiTrudiMatrix ξ L).det := by
  rw [Matrix.det_succ_row _ (Fin.last L)]
  rw [Finset.sum_eq_single (Fin.last L)]
  · have hrow := rowLength_eq_zero ξ hL
    simp only [jacobiTrudiMatrix, Fin.val_last, hrow, Nat.cast_zero,
      zero_sub, neg_add_cancel, completeInt_zero, mul_one, Fin.succAbove_last]
    have hs : (-1 : SymmetricFunction R) ^ (L + L) = 1 := by
      rw [pow_add, ← mul_pow]
      simp
    rw [hs, one_mul]
    rfl
  · intro j _ hj
    have hjL : (j : ℕ) < L := by
      have := j.isLt
      have : (j : ℕ) ≠ L := by simpa [Fin.ext_iff] using hj
      omega
    have hz : jacobiTrudiMatrix (R := R) ξ (L + 1) (Fin.last L) j = 0 := by
      apply completeInt_of_neg
      simp only [Fin.val_last, rowLength_eq_zero ξ hL, Nat.cast_zero]
      omega
    rw [hz, mul_zero, zero_mul]
  · simp

/-- Sufficient zero padding does not change the Schur function. -/
theorem det_jacobiTrudiMatrix (ξ : Nat.Partition d) {L : ℕ} (hL : length ξ ≤ L) :
    (jacobiTrudiMatrix (R := R) ξ L).det = schur ξ := by
  induction L, hL using Nat.le_induction with
  | base => rfl
  | succ L hL ih => rw [det_jacobiTrudiMatrix_succ ξ hL, ih]

/-- Each nonzero determinant term has symmetric-function degree d. -/
theorem isHomogeneous_det_jacobiTrudiMatrix (ξ : Nat.Partition d) {L : ℕ}
    (hL : length ξ ≤ L) :
    IsHomogeneous (jacobiTrudiMatrix (R := R) ξ L).det d := by
  classical
  rw [Matrix.det_apply]
  apply (homogeneousSubmodule R d).sum_mem
  intro σ _
  change (Equiv.Perm.sign σ : ℤ) • _ ∈ homogeneousSubmodule R d
  apply (homogeneousSubmodule R d).toAddSubgroup.zsmul_mem
  let a : Fin L → ℤ := fun i => (rowLength ξ (σ i) : ℤ) - (σ i : ℤ) + (i : ℤ)
  by_cases ha : ∀ i, 0 ≤ a i
  · have hrows : ∑ i : Fin L, (rowLength ξ i : ℤ) = (d : ℤ) := by
      exact_mod_cast (Fin.sum_univ_eq_sum_range (rowLength ξ) L).trans
        (sum_rowLength_padded ξ hL)
    have hsum : ∑ i, a i = (d : ℤ) := by
      simp only [a, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [Equiv.sum_comp σ (fun i : Fin L => (rowLength ξ i : ℤ)),
        Equiv.sum_comp σ (fun i : Fin L => (i : ℤ)), hrows]
      ring
    have hdeg : ∑ i, (a i).toNat = d := by
      apply Int.natCast_inj.mp
      simpa only [Nat.cast_sum, Int.toNat_of_nonneg (ha _)] using hsum
    have hp := SetLike.prod_mem_graded (homogeneousSubmodule R)
      (fun i => (a i).toNat) (fun i => jacobiTrudiMatrix (R := R) ξ L (σ i) i)
      (F := Finset.univ) (fun i _ => by
        change IsHomogeneous (completeInt (a i)) (a i).toNat
        simp only [completeInt, ha i, ite_true]
        exact isHomogeneous_h _)
    rwa [hdeg] at hp
  · obtain ⟨i, hi⟩ := not_forall.mp ha
    have hz : ∏ j, jacobiTrudiMatrix (R := R) ξ L (σ j) j = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact completeInt_of_neg (lt_of_not_ge hi)
    rw [hz]
    exact (homogeneousSubmodule R d).zero_mem

/-- Schur functions are homogeneous in the size of their partition. -/
@[simp] theorem isHomogeneous_schur (ξ : Nat.Partition d) :
    IsHomogeneous (schur (R := R) ξ) d :=
  isHomogeneous_det_jacobiTrudiMatrix ξ le_rfl

@[simp] theorem schur_zero (ξ : Nat.Partition 0) : schur (R := R) ξ = 1 := by
  simp [schur]

/-- The one-row Schur function, including the empty partition at n=0. -/
@[simp] theorem schur_indiscrete (n : ℕ) :
    schur (R := R) (Nat.Partition.indiscrete n) = h n := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [schur, length_indiscrete hn, Matrix.det_fin_one]
  simp [jacobiTrudiMatrix]

/-- Coefficient change commutes with the actual determinant. -/
@[simp] theorem map_schur (φ : R →+* S) (ξ : Nat.Partition d) :
    map φ (schur ξ) = schur ξ := by
  rw [schur, RingHom.map_det]
  congr 1
  ext i j
  exact map_completeInt φ _

/-- Finite complete polynomials extended by zero at negative integer indices. -/
def finiteCompleteInt (N : ℕ) (k : ℤ) : MvPolynomial (Fin N) R :=
  if 0 ≤ k then MvPolynomial.hsymm (Fin N) R k.toNat else 0

@[simp] theorem rho_completeInt (N : ℕ) (k : ℤ) :
    (rho R N (completeInt k) : MvPolynomial (Fin N) R) = finiteCompleteInt N k := by
  unfold completeInt finiteCompleteInt
  split_ifs <;> simp [rho_h]

/-- Finite specialization is the same determinant of finite complete polynomials.
No bound on the alphabet size is assumed. -/
theorem rho_schur (N : ℕ) (ξ : Nat.Partition d) :
    (rho R N (schur ξ) : MvPolynomial (Fin N) R) =
      Matrix.det (fun i j : Fin (length ξ) => finiteCompleteInt (R := R) N
        ((rowLength ξ i : ℤ) - (i : ℤ) + (j : ℤ))) := by
  let φ := (MvPolynomial.symmetricSubalgebra (Fin N) R).val.comp (rho R N)
  change φ (schur ξ) = _
  rw [schur, AlgHom.map_det]
  congr 1
  funext i j
  exact rho_completeInt (R := R) N _

end
end SymmetricFunction
