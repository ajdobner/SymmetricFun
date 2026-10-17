import SymmetricFunctions.Hall.Hopf
import SymmetricFunctions.Finite.CompleteCoefficients

/-! # Integral symmetry of the Hall pairing by transposition of exponent matrices -/

noncomputable section
open scoped TensorProduct
namespace SymmetricFunction
open SymmetricFunctions SymmetricFunctions.Series
variable {R σ τ : Type*} [CommRing R] [Fintype σ] [Fintype τ]

open Classical in
/-- Complete functions specialize to complete polynomials in every finite alphabet. -/
@[simp] theorem alphabetSpecialization_h (n : ℕ) :
    alphabetSpecialization R σ (h n) = MvPolynomial.hsymm σ R n := by
  classical
  rw [← rename_alphabetSpecialization (Fintype.equivFin σ).symm,
    alphabetSpecialization_fin, rho_h, MvPolynomial.rename_hsymm]

/-- Include the zero entries when writing a complete exponent product. -/
theorem hPart_exponentPartition_eq_prod (a : σ →₀ ℕ) :
    hPart (R := R) (exponentPartition a).2 = ∏ i, h (a i) := by
  rw [hPart_exponentPartition]
  exact Finsupp.prod_fintype _ _ (fun _ => h_zero)

omit [Fintype σ] in
/-- Hall pairings of complete products count nonnegative integer matrices. -/
theorem hall_complete_exponents [Finite σ] (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    hall (hPart (R := R) (exponentPartition a).2) (hPart (exponentPartition b).2) =
      (marginMatrices b a).card := by
  classical
  let := Fintype.ofFinite σ
  rw [hall_hPart_eq_coeff, hPart_exponentPartition_eq_prod, map_prod]
  simp_rw [alphabetSpecialization_h]
  exact coeff_prod_hsymm b a

omit [Fintype σ] [Fintype τ] in
/-- Transposing a matrix proves symmetry on complete exponent products. -/
theorem hall_complete_exponents_symm [Finite σ] [Finite τ] (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    hall (hPart (R := R) (exponentPartition a).2) (hPart (exponentPartition b).2) =
      hall (hPart (exponentPartition b).2) (hPart (exponentPartition a).2) := by
  let := Fintype.ofFinite σ
  let := Fintype.ofFinite τ
  rw [hall_complete_exponents, hall_complete_exponents, card_marginMatrices_comm]

/-- Symmetry on the actual complete partition basis. -/
theorem hall_hPart_symm (μ ν : Σ d, Nat.Partition d) :
    hall (hPart (R := R) μ.2) (hPart ν.2) = hall (hPart ν.2) (hPart μ.2) := by
  have hm : exponentPartition (Partition.representative μ.2) = μ :=
    (exponentPartition_eq_iff _ _).mpr (Partition.exponentParts_representative _)
  have hn : exponentPartition (Partition.representative ν.2) = ν :=
    (exponentPartition_eq_iff _ _).mpr (Partition.exponentParts_representative _)
  have he := hall_complete_exponents_symm (R := R)
    (Partition.representative μ.2) (Partition.representative ν.2)
  rw [hm, hn] at he
  exact he

/-- The classical Hall pairing is symmetric over every commutative ring. -/
theorem hall_symm (f g : SymmetricFunction R) : hall f g = hall g f := by
  have he : (hall (R := R)) = hall.flip := by
    apply (hBasisAll R).ext
    intro μ
    apply (hBasisAll R).ext
    intro ν
    change hall (hBasisAll R μ) (hBasisAll R ν) = hall (hBasisAll R ν) (hBasisAll R μ)
    rw [hBasisAll_apply, hBasisAll_apply]
    exact hall_hPart_symm μ ν
  exact LinearMap.congr_fun (LinearMap.congr_fun he f) g

/-- The product pairing inherits symmetry. -/
theorem tensorHall_symm (x y : SymmetricFunction R ⊗[R] SymmetricFunction R) :
    tensorHall x y = tensorHall y x := by
  exact (LinearMap.IsSymm.tmul (B₁ := hall) (B₂ := hall) ⟨hall_symm⟩ ⟨hall_symm⟩).eq x y

/-- The adjunction in the second variable, with the product tensor pairing. -/
theorem hall_mul_right (f g k : SymmetricFunction R) :
    hall f (g * k) = tensorHall (comultiplication f) (g ⊗ₜ[R] k) := by
  rw [hall_symm, hall_mul, tensorHall_symm]

/-- A one-row pairing is the coefficient in a single actual alphabet variable. -/
theorem hall_h_eq_coeff (n : ℕ) (f : SymmetricFunction R) :
    hall (h n) f = (alphabetSpecialization R (Fin 1) f).coeff (Finsupp.single 0 n) := by
  have he := hall_hPart_eq_coeff (R := R) (Finsupp.single (0 : Fin 1) n) f
  rw [hPart_exponentPartition, Finsupp.prod_single_index (by simp only [h_zero])] at he
  exact he

open Classical in
/-- Complete functions in single rows pair to the degree Kronecker delta. -/
theorem hall_h_h (n m : ℕ) :
    hall (h (R := R) n) (h m) = if n = m then 1 else 0 := by
  rw [hall_h_eq_coeff, alphabetSpecialization_h, coeff_hsymm]
  simp only [finsupp_degree_eq_sum, Fin.sum_univ_one, Finsupp.single_eq_same]

end SymmetricFunction
