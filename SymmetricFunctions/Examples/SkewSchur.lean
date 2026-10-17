import SymmetricFunctions.Schur.SkewDeterminant
import Mathlib.Data.ZMod.Basic

/-! # Bounded skewing conventions and the finite coproduct expansion -/

noncomputable section
open scoped TensorProduct
namespace SymmetricFunction.Examples
variable {R : Type*} [CommRing R]

example (f : SymmetricFunction R) : skewing 1 f = f := by simp
example (f : SymmetricFunction R) : skewing 0 f = 0 := by simp
example : skewing (h (R := R) 2) (h 1) = 0 :=
  skewing_eq_zero_of_degree_lt (isHomogeneous_h 2) (isHomogeneous_h 1) (by decide)

example {d : ℕ} (ξ : Nat.Partition d) (μ : Nat.Partition 0) :
    skewSchur (R := R) ξ μ = schur ξ := by simp

example {d : ℕ} (ξ : Nat.Partition d) : skewSchur (R := ZMod 6) ξ ξ = 1 := by simp

example : skewJacobiTrudiMatrix (R := R)
    (Nat.Partition.indiscrete 1) (Nat.Partition.indiscrete 3) 1 0 0 = 0 := by
  simp [skewJacobiTrudiMatrix, SymmetricFunctions.Partition.rowLength_indiscrete]

example (f g k : SymmetricFunction (ZMod 6)) :
    hall (skewing f g) k = hall g (f * k) := hall_skewing f g k

example {d : ℕ} (ξ : Nat.Partition d) :
    comultiplication (schur (R := R) ξ) =
      ∑ n ∈ Finset.range (d + 1), ∑ μ : Nat.Partition n, skewSchur ξ μ ⊗ₜ[R] schur μ :=
  comultiplication_schur ξ

-- The determinant identity permits independent extra padding of both shapes.
example {d e : ℕ} (ξ : Nat.Partition d) (μ : Nat.Partition e) :
    (skewJacobiTrudiMatrix (R := ZMod 6) ξ μ
      (SymmetricFunctions.Partition.length ξ + SymmetricFunctions.Partition.length μ + 3)).det =
      skewSchur ξ μ := skew_jacobiTrudi ξ μ (by omega) (by omega)

-- A nonempty skew row gives the expected complete function.
example : skewSchur (R := R) (Nat.Partition.indiscrete 3) (Nat.Partition.indiscrete 1) = h 2 := by
  rw [← skew_jacobiTrudi (N := 1) _ _ (by decide) (by decide), Matrix.det_fin_one]
  norm_num [skewJacobiTrudiMatrix, SymmetricFunctions.Partition.rowLength_indiscrete, completeInt]

-- Size 2 is smaller than size 3, but the two-row inner diagram does not fit a row.
private def skewShape11 : Nat.Partition 2 := Nat.Partition.ofSums 2 {1, 1} (by decide)

example : skewSchur (R := R) (Nat.Partition.indiscrete 3) skewShape11 = 0 := by
  apply skewSchur_eq_zero_of_not_contained
  intro hc
  have hrow := (SymmetricFunctions.Partition.contained_iff_rowLength _ _).mp hc 1
  have hp : 0 < SymmetricFunctions.Partition.rowLength skewShape11 1 :=
    (SymmetricFunctions.Partition.rowLength_pos_iff _ _).mpr (by decide)
  simp only [SymmetricFunctions.Partition.rowLength_indiscrete, Nat.one_ne_zero, ite_false] at hrow
  omega

end SymmetricFunction.Examples
