import SymmetricFunctions.Cauchy.Finite
import SymmetricFunctions.Completion.TensorSpecialization
import SymmetricFunctions.Hall.Symmetry

/-! # Integral complete–monomial Cauchy components

Partition size d contributes total tensor degree 2*d, because both factors
have degree d. The finite-alphabet product has precisely these components.
-/
noncomputable section
namespace SymmetricFunction
open SymmetricFunctions SymmetricFunctions.Series
open scoped TensorProduct
variable {R : Type*} [CommRing R]

/-- In a fixed degree, pairing against monomials gives the complete-basis coordinates. -/
theorem hall_mPart_homogeneous {d : ℕ} (f : homogeneousSubmodule R d) (μ : Nat.Partition d) :
    hall f.val (mPart μ) = (hBasis R d).repr f μ := by
  rw [hall_mPart f.val (⟨d, μ⟩ : Σ d, Nat.Partition d), hBasisAll_repr, hBasis_repr]

/-- The finite dual-basis reconstruction in one homogeneous degree. -/
theorem sum_hall_mPart_smul_hPart {d : ℕ} (f : homogeneousSubmodule R d) :
    (∑ μ : Nat.Partition d, hall f.val (mPart μ) • hPart μ) = f.val := by
  have he := congrArg Subtype.val ((hBasis R d).sum_repr f)
  simpa only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, hBasis_apply,
    ← hall_mPart_homogeneous] using he

/-- The size-d complete–monomial kernel, still a finite bounded tensor. -/
def cauchyCompleteMonomialComponent (R : Type*) [CommRing R] (d : ℕ) :
    SymmetricFunction R ⊗[R] SymmetricFunction R :=
  ∑ μ : Nat.Partition d, hPart μ ⊗ₜ[R] mPart μ

/-- Both factors count: partition size d gives total degree 2*d. -/
theorem cauchyCompleteMonomialComponent_mem (d : ℕ) :
    cauchyCompleteMonomialComponent R d ∈ tensorDegree R (2 * d) := by
  apply (tensorDegree R (2 * d)).sum_mem
  intro μ _
  simpa only [two_mul] using tmul_mem_tensorDegree (isHomogeneous_hPart μ) (isHomogeneous_mPart μ)

/-- Finite specialization extracts a complete product in the left alphabet. -/
theorem coeff_cauchyCompleteMonomialComponent (M N d : ℕ)
    (a : Fin M →₀ ℕ) (b : Fin N →₀ ℕ) :
    (tensorAlphabetSpecialization R (Fin M) (Fin N)
      (cauchyCompleteMonomialComponent R d)).coeff (a.sumElim b) =
        if b.degree = d then MvPowerSeries.coeff (a.sumElim b)
          (finiteCauchyProduct (Fin M) (Fin N) R) else 0 := by
  classical
  rw [cauchyCompleteMonomialComponent, map_sum, MvPolynomial.coeff_sum]
  simp_rw [tensorAlphabetSpecialization_tmul, MvPolynomial.coeff_sumElim_rename_mul,
    ← hall_hPart_eq_coeff b]
  by_cases hb : b.degree = d
  · rw [ite_eq_left hb]
    let f : homogeneousSubmodule R d := ⟨hPart (exponentPartition b).2, by
      change IsHomogeneous (hPart (R := R) (exponentPartition b).2) d
      simpa only [exponentPartition_degree, hb] using
        isHomogeneous_hPart (R := R) (exponentPartition b).2⟩
    have he := congrArg (fun g => (alphabetSpecialization R (Fin M) g).coeff a)
      (sum_hall_mPart_smul_hPart f)
    simp only [map_sum, map_smul, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
      smul_eq_mul] at he
    rw [coeff_finiteCauchyProduct]
    calc
      _ = (alphabetSpecialization R (Fin M) f.val).coeff a := by
        rw [← he]
        apply Finset.sum_congr rfl
        intro μ _
        exact mul_comm _ _
      _ = _ := by
        change (alphabetSpecialization R (Fin M) (hPart (exponentPartition b).2)).coeff a = _
        rw [hPart_exponentPartition_eq_prod, map_prod]
        simp_rw [alphabetSpecialization_h]
  · rw [ite_eq_right hb]
    apply Finset.sum_eq_zero
    intro μ _
    rw [hall_eq_zero_of_degrees_ne (isHomogeneous_hPart (exponentPartition b).2)
      (isHomogeneous_mPart μ) hb, mul_zero]

/-- Even total layers of the finite Cauchy product are exactly the h/m expansion. -/
theorem homogeneousComponent_finiteCauchyProduct_even (M N d : ℕ) :
    MvPowerSeries.homogeneousComponent (2 * d) (finiteCauchyProduct (Fin M) (Fin N) R) =
      (tensorAlphabetSpecialization R (Fin M) (Fin N)
        (cauchyCompleteMonomialComponent R d) : MvPowerSeries (Fin M ⊕ Fin N) R) := by
  classical
  apply MvPowerSeries.ext
  intro c
  obtain ⟨a, b, rfl⟩ : ∃ (a : Fin M →₀ ℕ) (b : Fin N →₀ ℕ), c = a.sumElim b :=
    ⟨_, _, (Finsupp.comapDomain_sumElim_comapDomain c).symm⟩
  rw [MvPowerSeries.coeff_homogeneousComponent, MvPolynomial.coeff_coe,
    coeff_cauchyCompleteMonomialComponent]
  have hd : (a.sumElim b).degree = a.degree + b.degree := by
    rw [Finsupp.sumElim_eq_add, map_add, Finsupp.degree_mapDomain, Finsupp.degree_mapDomain]
  rw [hd]
  by_cases hab : a.degree = b.degree
  · by_cases hb : b.degree = d
    · simp only [hab, hb, ← two_mul, ite_true]
    · have hn : a.degree + b.degree ≠ 2 * d := by omega
      rw [ite_eq_right hn, ite_eq_right hb]
  · rw [coeff_finiteCauchyProduct_eq_zero _ _ _ a b hab]
    simp

/-- Odd total layers vanish: Cauchy coefficients have equal degrees in both alphabets. -/
theorem homogeneousComponent_finiteCauchyProduct_odd (M N d : ℕ) :
    MvPowerSeries.homogeneousComponent (2 * d + 1)
      (finiteCauchyProduct (Fin M) (Fin N) R) = 0 := by
  classical
  apply MvPowerSeries.ext
  intro c
  obtain ⟨a, b, rfl⟩ : ∃ (a : Fin M →₀ ℕ) (b : Fin N →₀ ℕ), c = a.sumElim b :=
    ⟨_, _, (Finsupp.comapDomain_sumElim_comapDomain c).symm⟩
  rw [MvPowerSeries.coeff_homogeneousComponent, map_zero]
  by_cases hab : a.degree = b.degree
  · have hd : (a.sumElim b).degree = a.degree + b.degree := by
      rw [Finsupp.sumElim_eq_add, map_add, Finsupp.degree_mapDomain, Finsupp.degree_mapDomain]
    exact ite_eq_right (by omega)
  · rw [coeff_finiteCauchyProduct_eq_zero _ _ _ a b hab]
    simp

end SymmetricFunction
