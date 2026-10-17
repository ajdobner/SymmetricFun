import SymmetricFunctions.Hall.Symmetry
import Mathlib.Data.ZMod.Basic

/-! # Hall normalization, repeated parts, grading and torsion checks -/

noncomputable section
open scoped TensorProduct
namespace SymmetricFunction.Examples
variable {R : Type*} [CommRing R]

example (μ : Nat.Partition 0) : hall (hPart (R := R) μ) (mPart μ) = 1 := by
  simpa using hall_hPart_mPart (R := R) ⟨0, μ⟩ ⟨0, μ⟩

private def repeated22 : Nat.Partition 4 := Nat.Partition.ofSums 4 {2, 2} (by decide)

private theorem hPart_repeated22 : hPart (R := R) repeated22 = h 2 ^ 2 := by
  norm_num [hPart, repeated22, Nat.Partition.ofSums, pow_two, Multiset.filter_singleton]

-- The repeated parts are not divided by their stabilizer cardinal.
example : hall (h (R := ZMod 6) 2 ^ 2) (mPart repeated22) = 1 := by
  rw [← hPart_repeated22]
  simpa using hall_hPart_mPart (R := ZMod 6) ⟨4, repeated22⟩ ⟨4, repeated22⟩

example : hall (h (R := R) 2) (h 3) = 0 := by simp [hall_h_h]
example : hall (h (R := R) 2) (h 2) = 1 := by simp [hall_h_h]

-- A degree-two polynomial is tested in one actual variable, not a virtual alphabet.
example : hall (h (R := R) 2) (h 1 ^ 2) = 1 := by
  rw [hall_h_eq_coeff, map_pow, alphabetSpecialization_h]
  simp [MvPolynomial.hsymm_one, MvPolynomial.coeff_X_pow]

example (f g k : SymmetricFunction (ZMod 6)) :
    hall (f * g) k = tensorHall (f ⊗ₜ[ZMod 6] g) (comultiplication k) := hall_mul f g k

example (d : ℕ) (f : homogeneousSubmodule PUnit d) :
    (hallHomogeneousPerfect PUnit d).symm (hallHomogeneousPerfect PUnit d f) = f := by simp

example {d e : ℕ} (f : homogeneousSubmodule R d) (g : homogeneousSubmodule R e)
    (hne : d ≠ e) : hall (f : SymmetricFunction R) g = 0 :=
  hall_eq_zero_of_degrees_ne f.property g.property hne

end SymmetricFunction.Examples
