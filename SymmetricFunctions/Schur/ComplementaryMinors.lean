import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Complementary block determinants over arbitrary rings

The proof uses block multiplication, not division by a proper minor. Empty
blocks and the zero ring are permitted. Shape reindexing and its signs are
separate from this algebraic identity.
-/

namespace SymmetricFunctions

open Matrix

variable {R I J : Type*} [CommRing R] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

/-- Complementary principal blocks of a matrix and a right inverse. -/
theorem det_block_eq_det_mul_complement
    (A B : Matrix (I ⊕ J) (I ⊕ J) R) (hAB : A * B = 1) :
    A.toBlocks₁₁.det = A.det * B.toBlocks₂₂.det := by
  have h12 : A.toBlocks₁₁ * B.toBlocks₁₂ + A.toBlocks₁₂ * B.toBlocks₂₂ = 0 := by
    have h := congrArg Matrix.toBlocks₁₂ hAB
    rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply] at h
    have ho : (1 : Matrix (I ⊕ J) (I ⊕ J) R).toBlocks₁₂ = 0 := by
      ext i j
      simp [toBlocks₁₂, one_apply]
    simpa only [toBlocks_fromBlocks₁₂, ho] using h
  have h22 : A.toBlocks₂₁ * B.toBlocks₁₂ + A.toBlocks₂₂ * B.toBlocks₂₂ = 1 := by
    have h := congrArg Matrix.toBlocks₂₂ hAB
    rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply] at h
    have ho : (1 : Matrix (I ⊕ J) (I ⊕ J) R).toBlocks₂₂ = 1 := by
      ext i j
      simp [toBlocks₂₂, one_apply]
    simpa only [toBlocks_fromBlocks₂₂, ho] using h
  have hmul : A * fromBlocks (1 : Matrix I I R) B.toBlocks₁₂ 0 B.toBlocks₂₂ =
      fromBlocks A.toBlocks₁₁ 0 A.toBlocks₂₁ (1 : Matrix J J R) := by
    conv_lhs => rw [← fromBlocks_toBlocks A]
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, h12, h22]
  have hd := congrArg Matrix.det hmul
  simpa only [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂,
    det_one, one_mul, mul_one] using hd.symm

/-- Complementary minors after independent row and column reindexing.
The determinant of the reindexed full matrix retains the permutation signs. -/
theorem det_minor_eq_det_mul_complement {K : Type*} [Fintype K] [DecidableEq K]
    (A B : Matrix K K R) (hAB : A * B = 1) (r c : I ⊕ J ≃ K) :
    (A.submatrix (r ∘ Sum.inl) (c ∘ Sum.inl)).det =
      (A.submatrix r c).det * (B.submatrix (c ∘ Sum.inr) (r ∘ Sum.inr)).det := by
  apply det_block_eq_det_mul_complement (A.submatrix r c) (B.submatrix c r)
  rw [Matrix.submatrix_mul_equiv, hAB, Matrix.submatrix_one_equiv]

end SymmetricFunctions
