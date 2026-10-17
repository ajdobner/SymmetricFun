import SymmetricFunctions.Hopf.Basic

/-! # Comultiplication specializes to addition of disjoint finite alphabets -/

noncomputable section

namespace SymmetricFunctions

variable {σ τ R : Type*} [Fintype σ] [Fintype τ] [CommRing R]

/-- Elementary polynomials in a disjoint union of alphabets satisfy convolution. -/
theorem esymm_sum_alphabet (n : ℕ) :
    MvPolynomial.esymm (σ ⊕ τ) R n =
      ∑ ij ∈ Finset.antidiagonal n,
        MvPolynomial.rename Sum.inl (MvPolynomial.esymm σ R ij.1) *
          MvPolynomial.rename Sum.inr (MvPolynomial.esymm τ R ij.2) := by
  classical
  have he : elementarySeries (σ ⊕ τ) R =
      PowerSeries.map (MvPolynomial.rename Sum.inl).toRingHom (elementarySeries σ R) *
        PowerSeries.map (MvPolynomial.rename Sum.inr).toRingHom (elementarySeries τ R) := by
    simp [elementarySeries, Fintype.prod_sum_type]
  have hc := congrArg (PowerSeries.coeff n) he
  simp only [coeff_elementarySeries, PowerSeries.coeff_mul, PowerSeries.coeff_map,
    map_mul, map_pow, map_neg, map_one] at hc
  apply (isUnit_neg_one.pow n).mul_left_cancel
  rw [hc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [← Finset.mem_antidiagonal.mp hij, pow_add]
  ring_nf
  rfl

end SymmetricFunctions

namespace SymmetricFunction

open scoped TensorProduct

variable (R : Type*) [CommRing R]

/-- Specialization to a finite alphabet, as an ordinary polynomial algebra map. -/
def alphabetSpecialization (σ : Type*) [Fintype σ] :
    SymmetricFunction R →ₐ[R] MvPolynomial σ R :=
  eval (fun n : ℕ+ => MvPolynomial.esymm σ R n)

@[simp] theorem alphabetSpecialization_e (σ : Type*) [Fintype σ] (n : ℕ) :
    alphabetSpecialization R σ (e n) = MvPolynomial.esymm σ R n := by
  cases n with
  | zero => simp [MvPolynomial.esymm_zero]
  | succ n => exact eval_e_succ _ n

/-- On Fin N this is the polynomial underlying the existing symmetric specialization. -/
theorem alphabetSpecialization_fin (N : ℕ) (f : SymmetricFunction R) :
    alphabetSpecialization R (Fin N) f = (rho R N f : MvPolynomial (Fin N) R) := by
  have he : alphabetSpecialization R (Fin N) =
      (MvPolynomial.symmetricSubalgebra (Fin N) R).val.comp (rho R N) := by
    apply algHom_ext
    intro i
    simp [rho_e]
  exact DFunLike.congr_fun he f

/-- Specialize the two tensor factors in independent alphabets and multiply. -/
def tensorAlphabetSpecialization (σ τ : Type*) [Fintype σ] [Fintype τ] :
    (SymmetricFunction R ⊗[R] SymmetricFunction R) →ₐ[R] MvPolynomial (σ ⊕ τ) R :=
  Algebra.TensorProduct.lift
    ((MvPolynomial.rename Sum.inl).comp (alphabetSpecialization R σ))
    ((MvPolynomial.rename Sum.inr).comp (alphabetSpecialization R τ))
    (fun _ _ => Commute.all _ _)

@[simp] theorem tensorAlphabetSpecialization_tmul (σ τ : Type*) [Fintype σ] [Fintype τ]
    (f g : SymmetricFunction R) :
    tensorAlphabetSpecialization R σ τ (f ⊗ₜ[R] g) =
      MvPolynomial.rename Sum.inl (alphabetSpecialization R σ f) *
        MvPolynomial.rename Sum.inr (alphabetSpecialization R τ g) := by
  simp [tensorAlphabetSpecialization]

/-- The standard coproduct is precisely addition of disjoint finite alphabets. -/
theorem tensorAlphabetSpecialization_comp_comultiplication
    (σ τ : Type*) [Fintype σ] [Fintype τ] :
    (tensorAlphabetSpecialization R σ τ).comp comultiplication =
      alphabetSpecialization R (σ ⊕ τ) := by
  apply algHom_ext
  intro i
  simp only [AlgHom.comp_apply, comultiplication_e, map_sum,
    tensorAlphabetSpecialization_tmul, alphabetSpecialization_e]
  exact (SymmetricFunctions.esymm_sum_alphabet (R := R) (σ := σ) (τ := τ) i).symm

@[simp] theorem tensorAlphabetSpecialization_comultiplication
    (σ τ : Type*) [Fintype σ] [Fintype τ] (f : SymmetricFunction R) :
    tensorAlphabetSpecialization R σ τ (comultiplication f) =
      alphabetSpecialization R (σ ⊕ τ) f :=
  DFunLike.congr_fun (tensorAlphabetSpecialization_comp_comultiplication R σ τ) f

end SymmetricFunction
