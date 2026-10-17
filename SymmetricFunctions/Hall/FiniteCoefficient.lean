import SymmetricFunctions.Hall.Basic
import SymmetricFunctions.Hopf.Alphabets
import SymmetricFunctions.Realization.SeriesBasic

/-! # Hall pairings as actual finite-alphabet coefficients -/

noncomputable section
namespace MvPolynomial

variable {σ τ R : Type*} [CommRing R]

/-- Independent alphabets have independent coefficient extraction. -/
theorem coeff_sumElim_rename_mul (f : MvPolynomial σ R) (g : MvPolynomial τ R)
    (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    (rename Sum.inl f * rename Sum.inr g).coeff (a.sumElim b) = f.coeff a * g.coeff b := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f f' hf hf' => simp [add_mul, hf, hf']
  | monomial u r =>
    induction g using MvPolynomial.induction_on' with
    | add g g' hg hg' => simp [mul_add, hg, hg']
    | monomial v s =>
      rw [rename_monomial, rename_monomial, monomial_mul_monomial, ← Finsupp.sumElim_eq_add]
      have he : u.sumElim v = a.sumElim b ↔ u = a ∧ v = b := by
        constructor
        · intro h
          exact ⟨Finsupp.ext fun i => congrArg (fun c => c (Sum.inl i)) h,
            Finsupp.ext fun j => congrArg (fun c => c (Sum.inr j)) h⟩
        · rintro ⟨rfl, rfl⟩; rfl
      simp only [coeff_monomial, he]
      split_ifs <;> simp_all

end MvPolynomial

namespace SymmetricFunction

open SymmetricFunctions SymmetricFunctions.Series
variable {R σ τ : Type*} [CommRing R] [Fintype σ] [Fintype τ]

/-- Renaming a finite alphabet along an equivalence commutes with specialization. -/
theorem rename_alphabetSpecialization (e : σ ≃ τ) (f : SymmetricFunction R) :
    MvPolynomial.rename e (alphabetSpecialization R σ f) = alphabetSpecialization R τ f := by
  have he : (MvPolynomial.rename e).comp (alphabetSpecialization R σ) =
      alphabetSpecialization R τ := by
    apply algHom_ext
    intro i
    simp only [AlgHom.comp_apply, alphabetSpecialization_e, MvPolynomial.rename_esymm]
  exact DFunLike.congr_fun he f

open Classical in
/-- The monomial orbit realization in any finite alphabet. -/
@[simp] theorem alphabetSpecialization_mPart {d : ℕ} (μ : Nat.Partition d) :
    alphabetSpecialization R σ (mPart μ) = MvPolynomial.msymm σ R μ := by
  classical
  rw [← rename_alphabetSpecialization (Fintype.equivFin σ).symm,
    alphabetSpecialization_fin, rho_mPart, MvPolynomial.rename_msymm]

/-- The Hall pairing with the complete exponent product extracts a finite coefficient. -/
theorem hall_hPart_eq_coeff (a : σ →₀ ℕ) (f : SymmetricFunction R) :
    hall (hPart (exponentPartition a).2) f = (alphabetSpecialization R σ f).coeff a := by
  classical
  have he : hall (hPart (R := R) (exponentPartition a).2) =
      (MvPolynomial.lcoeff R a).comp (alphabetSpecialization R σ).toLinearMap := by
    apply (mBasisAll R).ext
    intro μ
    rw [mBasisAll_apply, hall_hPart_mPart (exponentPartition a) μ]
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, MvPolynomial.lcoeff_apply,
      alphabetSpecialization_mPart, MvPolynomial.coeff_msymm, exponentPartition_eq_iff]
  exact DFunLike.congr_fun he f

omit [Fintype σ] in
/-- Zero exponent entries contribute h₀=1; positive entries retain multiplicity. -/
theorem hPart_exponentPartition (a : σ →₀ ℕ) :
    hPart (R := R) (exponentPartition a).2 = a.prod (fun _ n => h n) := by
  simp only [hPart, exponentPartition_parts, exponentParts, Multiset.map_map,
    Finsupp.prod, Finset.prod_eq_multiset_prod]
  rfl

omit [Fintype σ] [Fintype τ] in
/-- Concatenating exponent alphabets multiplies their complete products. -/
theorem hPart_exponentPartition_sumElim (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    hPart (R := R) (exponentPartition (a.sumElim b)).2 =
      hPart (exponentPartition a).2 * hPart (exponentPartition b).2 := by
  simp only [hPart_exponentPartition, Finsupp.prod_sumElim, Function.comp_def]

end SymmetricFunction
