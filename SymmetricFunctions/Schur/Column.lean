import SymmetricFunctions.Schur.JacobiTrudi
import SymmetricFunctions.Schur.Toeplitz
import SymmetricFunctions.Hopf.Series
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # The one-column Jacobi–Trudi determinant

Finite upper triangular matrices carry the integral h/e inverse identity.
The adjugate's corner entry is the column determinant, with the expected sign.
-/

namespace SymmetricFunction

noncomputable section
open SymmetricFunctions SymmetricFunctions.Partition

variable {R : Type*} [CommRing R]

/-- The finite complete Toeplitz matrix uses the same integer-index convention. -/
theorem upperToeplitz_complete (N : ℕ) (i j : Fin N) :
    upperToeplitz N (completeGeneratingSeries (R := R)) i j =
      completeInt ((j : ℤ) - (i : ℤ)) := by
  by_cases hij : i ≤ j
  · rw [upperToeplitz_apply_le N _ hij, coeff_completeGeneratingSeries]
    have hn : 0 ≤ (j : ℤ) - (i : ℤ) := by omega
    simp only [completeInt, hn, ite_true]
    congr 1
    omega
  · rw [upperToeplitz_apply_gt N _ (lt_of_not_ge hij), completeInt_of_neg (by omega)]

/-- The one-column determinant is elementary, over an arbitrary coefficient ring. -/
@[simp] theorem schur_indiscrete_conjugate (n : ℕ) :
    schur (R := R) (Nat.Partition.indiscrete n).conjugate = e n := by
  let H := upperToeplitz (n + 1) (completeGeneratingSeries (R := R))
  let E := upperToeplitz (n + 1)
    (PowerSeries.rescale (-1) (elementaryGeneratingSeries (R := R)))
  have hEH : E * H = 1 := by
    rw [← upperToeplitz_mul, elementary_complete_series, upperToeplitz_one]
  have hdet : H.det = 1 := by simp [H, det_upperToeplitz]
  have hadj : H.adjugate = E := by
    calc
      H.adjugate = (E * H) * H.adjugate := by rw [hEH, one_mul]
      _ = E := by rw [Matrix.mul_assoc, Matrix.mul_adjugate, hdet, one_smul, mul_one]
  have hminor : H.submatrix (Fin.last n).succAbove (0 : Fin (n + 1)).succAbove =
      jacobiTrudiMatrix (R := R) (Nat.Partition.indiscrete n).conjugate n := by
    funext i j
    simp only [Matrix.submatrix_apply, Fin.succAbove_last, Fin.succAbove_zero]
    dsimp only [H]
    rw [upperToeplitz_complete]
    dsimp only [jacobiTrudiMatrix]
    rw [rowLength_indiscrete_conjugate, ite_eq_left i.isLt]
    congr 1
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    ring
  have hc := congrArg (fun M => M (0 : Fin (n + 1)) (Fin.last n)) hadj
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, hminor,
    det_jacobiTrudiMatrix _ (by simp)] at hc
  have hsign : (-1 : SymmetricFunction R) ^ n *
      schur (Nat.Partition.indiscrete n).conjugate = (-1) ^ n * e n := by
    simpa [E, upperToeplitz, PowerSeries.coeff_rescale, mul_comm] using hc
  have hcancel := congrArg (fun x => (-1 : SymmetricFunction R) ^ n * x) hsign
  simpa [← mul_assoc, ← mul_pow] using hcancel

end
end SymmetricFunction
