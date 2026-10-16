import SymmetricFunctions.Schur.Skew
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

end SymmetricFunction.Examples
