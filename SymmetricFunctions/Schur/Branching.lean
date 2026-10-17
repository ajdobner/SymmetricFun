import SymmetricFunctions.Schur.HorizontalStrip
import SymmetricFunctions.Hall

/-! # Integral algebraic branching from the Hall coproduct -/
noncomputable section
namespace SymmetricFunction
open scoped TensorProduct
variable {R : Type*} [CommRing R]

/-- Move right-factor skewing across the explicit tensor Hall pairing. -/
theorem tensorHall_map_skewing (f a b : SymmetricFunction R)
    (z : SymmetricFunction R ⊗[R] SymmetricFunction R) :
    tensorHall (TensorProduct.map LinearMap.id (skewing f) z) (a ⊗ₜ[R] b) =
      tensorHall z (a ⊗ₜ[R] (f * b)) := by
  induction z with
  | tmul x y => simp only [TensorProduct.map_tmul, LinearMap.id_apply,
      tensorHall_tmul, hall_skewing]
  | add z w hz hw =>
    simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hz hw

/-- Skewing on the bounded function commutes with the right coproduct factor. -/
theorem comultiplication_skewing (f g : SymmetricFunction R) :
    comultiplication (skewing f g) =
      TensorProduct.map LinearMap.id (skewing f) (comultiplication g) := by
  apply tensorHall_schur_ext
  intro ξ μ
  rw [tensorHall_map_skewing, ← hall_mul_right, ← hall_mul_right, hall_skewing]
  congr 1
  ring

/-- The intermediate shape expansion is finite and works over arbitrary commutative rings. -/
theorem comultiplication_skewSchur {d e : ℕ} (ξ : Nat.Partition d) (μ : Nat.Partition e) :
    comultiplication (skewSchur (R := R) ξ μ) =
      ∑ n ∈ Finset.range (d + 1), ∑ ν : Nat.Partition n,
        skewSchur ξ ν ⊗ₜ[R] skewSchur ν μ := by
  rw [skewSchur, comultiplication_skewing, comultiplication_schur]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply, skewSchur]

open Classical in
/-- Branch on the largest alphabet letter, with every intermediate size bounded by d. -/
theorem alphabetSpecialization_succ_skewSchur {d e : ℕ} (ξ : Nat.Partition d)
    (μ : Nat.Partition e) (N : ℕ) :
    alphabetSpecialization R (Fin (N + 1)) (skewSchur ξ μ) =
      ∑ n ∈ Finset.range (d + 1), ∑ ν : Nat.Partition n,
        if SymmetricFunctions.Partition.HorizontalStrip ν ξ then
          MvPolynomial.rename Fin.castSucc (alphabetSpecialization R (Fin N) (skewSchur ν μ)) *
            MvPolynomial.X (Fin.last N) ^ (d - n)
        else 0 := by
  classical
  let eqv : (Fin 1 ⊕ Fin N) ≃ Fin (N + 1) := (Equiv.sumComm _ _).trans finSumFinEquiv
  rw [← rename_alphabetSpecialization eqv,
    ← tensorAlphabetSpecialization_comultiplication, comultiplication_skewSchur]
  simp only [map_sum, tensorAlphabetSpecialization_tmul, map_mul, MvPolynomial.rename_rename]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro ν hν
  rw [alphabetSpecialization_one_skewSchur]
  split_ifs with hs
  · have hi : eqv ∘ Sum.inr = (Fin.castSucc : Fin N → Fin (N + 1)) := rfl
    have hz : eqv (Sum.inl (0 : Fin 1)) = Fin.last N := by
      apply Fin.ext
      simp [eqv]
    simp only [map_pow, MvPolynomial.rename_X, Function.comp_apply, hz, hi]
    exact mul_comm _ _
  · simp

end SymmetricFunction
