import SymmetricFunctions.Hall.Skewing

/-! # Skew Schur functions as the actual bounded multiplication adjoints -/

noncomputable section
namespace SymmetricFunction
open SymmetricFunctions.Partition
variable {R : Type*} [CommRing R]

/-- The skew Schur function, defined by the Hall adjoint of multiplication. -/
def skewSchur {d e : ℕ} (ξ : Nat.Partition d) (μ : Nat.Partition e) : SymmetricFunction R :=
  skewing (schur μ) (schur ξ)

/-- The skew determinant uses integer subtraction for both shape and row shifts. -/
def skewJacobiTrudiMatrix {d e : ℕ} (ξ : Nat.Partition d) (μ : Nat.Partition e) (L : ℕ) :
    Matrix (Fin L) (Fin L) (SymmetricFunction R) := fun i j =>
  completeInt ((rowLength ξ i : ℤ) - (rowLength μ j : ℤ) - (i : ℤ) + (j : ℤ))

/-- Skewing lowers symmetric-function degree by the size of the inner shape. -/
theorem isHomogeneous_skewSchur {d e : ℕ} (ξ : Nat.Partition d) (μ : Nat.Partition e) :
    IsHomogeneous (skewSchur (R := R) ξ μ) (d - e) :=
  isHomogeneous_skewing (isHomogeneous_schur μ) (isHomogeneous_schur ξ)

/-- An inner shape larger in size makes the skew function zero. -/
theorem skewSchur_eq_zero_of_size_lt {d e : ℕ} (ξ : Nat.Partition d) (μ : Nat.Partition e)
    (hde : d < e) : skewSchur (R := R) ξ μ = 0 :=
  skewing_eq_zero_of_degree_lt (isHomogeneous_schur μ) (isHomogeneous_schur ξ) hde

/-- Empty inner shapes recover the original Schur function. -/
@[simp] theorem skewSchur_empty {d : ℕ} (ξ : Nat.Partition d) (μ : Nat.Partition 0) :
    skewSchur (R := R) ξ μ = schur ξ := by simp [skewSchur]

/-- The defining skew adjunction. -/
theorem hall_skewSchur {d e : ℕ} (ξ : Nat.Partition d) (μ : Nat.Partition e)
    (f : SymmetricFunction R) : hall (skewSchur ξ μ) f = hall (schur ξ) (schur μ * f) :=
  hall_skewing _ _ _

/-- Equal shapes give the multiplicative unit, including the empty shape. -/
@[simp] theorem skewSchur_self {d : ℕ} (ξ : Nat.Partition d) : skewSchur (R := R) ξ ξ = 1 := by
  have hz : IsHomogeneous (skewSchur (R := R) ξ ξ) 0 := by
    simpa using isHomogeneous_skewSchur (R := R) ξ ξ
  obtain ⟨r, hr⟩ := (isHomogeneous_zero_iff _).mp hz
  have h11 : hall (1 : SymmetricFunction R) 1 = 1 := by
    simpa only [h_zero, ite_true] using hall_h_h (R := R) 0 0
  have hh := hall_skewSchur (R := R) ξ ξ 1
  rw [mul_one, hall_schur_schur (⟨d, ξ⟩ : Σ d, Nat.Partition d) ⟨d, ξ⟩,
    ite_eq_left rfl, hr, Algebra.algebraMap_eq_smul_one, map_smul,
    LinearMap.smul_apply, h11, smul_eq_mul, mul_one] at hh
  rw [hr, hh, map_one]

open scoped TensorProduct in
/-- The finite coproduct expansion, with the right partition degree explicitly bounded. -/
theorem comultiplication_schur {d : ℕ} (ξ : Nat.Partition d) :
    comultiplication (schur (R := R) ξ) =
      ∑ n ∈ Finset.range (d + 1), ∑ μ : Nat.Partition n, skewSchur ξ μ ⊗ₜ[R] schur μ :=
  tensor_schur_expansion (comultiplication_mem_tensorDegree (isHomogeneous_schur ξ))

end SymmetricFunction
