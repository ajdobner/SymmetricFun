import SymmetricFunctions.Hall.FiniteCoefficient

/-! # Multiplication and the actual alphabet-addition coproduct are Hall adjoints -/

noncomputable section
open scoped TensorProduct

namespace SymmetricFunction
open SymmetricFunctions SymmetricFunctions.Series
variable {R σ τ : Type*} [CommRing R] [Fintype σ] [Fintype τ]

/-- The tensor pairing extracts a coefficient in two disjoint finite alphabets. -/
theorem tensorHall_hPart_eq_coeff (a : σ →₀ ℕ) (b : τ →₀ ℕ)
    (z : SymmetricFunction R ⊗[R] SymmetricFunction R) :
    tensorHall (hPart (exponentPartition a).2 ⊗ₜ[R] hPart (exponentPartition b).2) z =
      (tensorAlphabetSpecialization R σ τ z).coeff (a.sumElim b) := by
  induction z with
  | tmul f g =>
    rw [tensorHall_tmul, tensorAlphabetSpecialization_tmul,
      MvPolynomial.coeff_sumElim_rename_mul, hall_hPart_eq_coeff, hall_hPart_eq_coeff]
  | add z w hz hw =>
    simpa only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using
      congrArg₂ (· + ·) hz hw

omit [Fintype σ] [Fintype τ] in
/-- Coefficient concatenation proves the adjunction on complete exponent products. -/
theorem hall_mul_exponentPartition [Finite σ] [Finite τ] (a : σ →₀ ℕ) (b : τ →₀ ℕ)
    (f : SymmetricFunction R) :
    hall (hPart (exponentPartition a).2 * hPart (exponentPartition b).2) f =
      tensorHall (hPart (exponentPartition a).2 ⊗ₜ[R] hPart (exponentPartition b).2)
        (comultiplication f) := by
  let := Fintype.ofFinite σ
  let := Fintype.ofFinite τ
  rw [← hPart_exponentPartition_sumElim, hall_hPart_eq_coeff,
    tensorHall_hPart_eq_coeff, tensorAlphabetSpecialization_comultiplication]

/-- Complete partition products are adjoint to the existing coproduct. -/
theorem hall_mul_hPart (μ ν : Σ d, Nat.Partition d) (f : SymmetricFunction R) :
    hall (hPart μ.2 * hPart ν.2) f =
      tensorHall (hPart μ.2 ⊗ₜ[R] hPart ν.2) (comultiplication f) := by
  have hm : exponentPartition (Partition.representative μ.2) = μ :=
    (exponentPartition_eq_iff _ _).mpr (Partition.exponentParts_representative _)
  have hn : exponentPartition (Partition.representative ν.2) = ν :=
    (exponentPartition_eq_iff _ _).mpr (Partition.exponentParts_representative _)
  have he := hall_mul_exponentPartition
    (Partition.representative μ.2) (Partition.representative ν.2) f
  rw [hm, hn] at he
  exact he

/-- The Hall multiplication–coproduct adjunction for arbitrary bounded functions. -/
theorem hall_mul (f g k : SymmetricFunction R) :
    hall (f * g) k = tensorHall (f ⊗ₜ[R] g) (comultiplication k) := by
  classical
  rw [← (hBasisAll R).linearCombination_repr f, ← (hBasisAll R).linearCombination_repr g]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, map_sum, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, TensorProduct.sum_tmul, TensorProduct.tmul_sum,
    TensorProduct.smul_tmul, TensorProduct.tmul_smul, hBasisAll_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro μ hμ
  apply Finset.sum_congr rfl
  intro ν hν
  rw [hall_mul_hPart ν μ]

end SymmetricFunction
