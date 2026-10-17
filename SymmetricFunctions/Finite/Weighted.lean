import SymmetricFunctions.Specialization
import SymmetricFunctions.Grading.Evaluation
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # The weighted finite elementary presentation -/

noncomputable section

namespace SymmetricFunctions

/-- Homogeneous substitution commutes with the projections onto each weight. -/
theorem weightedComponent_aeval {σ τ R M : Type*} [CommSemiring R] [AddCommMonoid M]
    (w : σ → M) (v : τ → M) (x : σ → MvPolynomial τ R)
    (hx : ∀ i, (x i).IsWeightedHomogeneous v (w i)) (p : MvPolynomial σ R) (d : M) :
    MvPolynomial.weightedHomogeneousComponent v d (MvPolynomial.aeval x p) =
      MvPolynomial.aeval x (MvPolynomial.weightedHomogeneousComponent w d p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a r =>
    have hm := MvPolynomial.isWeightedHomogeneous_monomial w a r rfl
    rw [MvPolynomial.weightedHomogeneousComponent_of_mem
      (weightedHomogeneous_aeval hm x hx), MvPolynomial.weightedHomogeneousComponent_of_mem hm]
    split_ifs <;> simp
  | add p q ihp ihq => simp only [map_add, ihp, ihq]

/-- An injective homogeneous substitution also reflects homogeneity. -/
theorem weightedHomogeneous_aeval_iff {σ τ R M : Type*}
    [CommSemiring R] [AddCommMonoid M] (w : σ → M) (v : τ → M)
    (x : σ → MvPolynomial τ R) (hx : ∀ i, (x i).IsWeightedHomogeneous v (w i))
    (hinj : Function.Injective (MvPolynomial.aeval (R := R) x)) (p : MvPolynomial σ R) (d : M) :
    (MvPolynomial.aeval x p).IsWeightedHomogeneous v d ↔ p.IsWeightedHomogeneous w d := by
  refine ⟨fun hp => ?_, fun hp => weightedHomogeneous_aeval hp x hx⟩
  have he : MvPolynomial.weightedHomogeneousComponent w d p = p := by
    apply hinj
    rw [← weightedComponent_aeval w v x hx p d]
    exact hp.weightedHomogeneousComponent_same
  rw [← he]
  exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _

/-- Finite elementary polynomials have their usual alphabet degree, including the zero cases. -/
theorem isHomogeneous_esymm (σ R : Type*) [Fintype σ] [CommSemiring R] (d : ℕ) :
    (MvPolynomial.esymm σ R d).IsHomogeneous d := by
  classical
  unfold MvPolynomial.esymm
  apply (MvPolynomial.homogeneousSubmodule σ R d).sum_mem
  intro t ht
  have hd := (Finset.mem_powersetCard.mp ht).2
  have hh := MvPolynomial.IsHomogeneous.prod t (fun i : σ => MvPolynomial.X (R := R) i)
    (fun _ => 1) (fun i _ => MvPolynomial.isHomogeneous_X R i)
  simpa [hd] using hh

end SymmetricFunctions

namespace SymmetricFunction

open MvPolynomial SymmetricFunctions

variable (R : Type*) [CommRing R]

/-- The finite elementary presentation, with generator `i` of weight `i+1`. -/
def finitePresentation (N : ℕ) :
    MvPolynomial (Fin N) R ≃ₐ[R] symmetricSubalgebra (Fin N) R :=
  esymmAlgEquiv (Fin N) R (Fintype.card_fin N)

theorem finitePresentation_apply (N : ℕ) (p : MvPolynomial (Fin N) R) :
    (finitePresentation R N p : MvPolynomial (Fin N) R) =
      aeval (fun i : Fin N => esymm (Fin N) R (i.val + 1)) p :=
  esymmAlgHom_apply p

/-- The finite fundamental theorem preserves and reflects weighted homogeneity. -/
theorem finitePresentation_homogeneous_iff (N d : ℕ) (p : MvPolynomial (Fin N) R) :
    (finitePresentation R N p : MvPolynomial (Fin N) R).IsHomogeneous d ↔
      p.IsWeightedHomogeneous (fun i : Fin N => i.val + 1) d := by
  rw [finitePresentation_apply]
  apply weightedHomogeneous_aeval_iff
  · exact fun i => isHomogeneous_esymm _ _ _
  · intro p q he
    apply (finitePresentation R N).injective
    apply Subtype.ext
    simpa only [finitePresentation_apply] using he

theorem finitePresentation_symm_homogeneous (N d : ℕ)
    (p : symmetricSubalgebra (Fin N) R) (hp : p.val.IsHomogeneous d) :
    ((finitePresentation R N).symm p).IsWeightedHomogeneous (fun i : Fin N => i.val + 1) d :=
  (finitePresentation_homogeneous_iff R N d _).mp (by simpa using hp)

/-- Regard a polynomial in the first `N` elementary generators as a symmetric function. -/
def finiteLift (N : ℕ) : MvPolynomial (Fin N) R →ₐ[R] SymmetricFunction R :=
  aeval (fun i : Fin N => e (i.val + 1))

@[simp] theorem finiteLift_X (N : ℕ) (i : Fin N) :
    finiteLift R N (X i) = e (i.val + 1) := by simp [finiteLift]

theorem rho_comp_finiteLift (N : ℕ) :
    (rho R N).comp (finiteLift R N) = (finitePresentation R N).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  apply Subtype.ext
  simp [finitePresentation_apply]

/-- Canonical lift of a finite symmetric polynomial by its elementary presentation. -/
def liftSymmetric (N : ℕ) : symmetricSubalgebra (Fin N) R →ₐ[R] SymmetricFunction R :=
  (finiteLift R N).comp (finitePresentation R N).symm.toAlgHom

@[simp] theorem rho_liftSymmetric (N : ℕ) (p : symmetricSubalgebra (Fin N) R) :
    rho R N (liftSymmetric R N p) = p := by
  change ((rho R N).comp (finiteLift R N)) ((finitePresentation R N).symm p) = p
  rw [rho_comp_finiteLift]
  exact (finitePresentation R N).apply_symm_apply p

theorem rho_surjective (N : ℕ) : Function.Surjective (rho R N) :=
  fun p => ⟨liftSymmetric R N p, rho_liftSymmetric R N p⟩

theorem isHomogeneous_finiteLift (N d : ℕ) (p : MvPolynomial (Fin N) R)
    (hp : p.IsWeightedHomogeneous (fun i : Fin N => i.val + 1) d) :
    IsHomogeneous (finiteLift R N p) d := by
  unfold IsHomogeneous
  have he : polynomialEquiv R (finiteLift R N p) =
      aeval (fun i : Fin N => polynomialEquiv R (e (R := R) (i.val + 1))) p :=
    MvPolynomial.comp_aeval_apply (fun i : Fin N => e (R := R) (i.val + 1))
      (polynomialEquiv R).toAlgHom p
  rw [he]
  exact weightedHomogeneous_aeval hp _ (fun i => isHomogeneous_e (i.val + 1))

theorem isHomogeneous_liftSymmetric (N d : ℕ) (p : symmetricSubalgebra (Fin N) R)
    (hp : p.val.IsHomogeneous d) : IsHomogeneous (liftSymmetric R N p) d :=
  isHomogeneous_finiteLift R N d _ (finitePresentation_symm_homogeneous R N d p hp)

theorem isHomogeneous_rho (N d : ℕ) (f : SymmetricFunction R) (hf : IsHomogeneous f d) :
    (rho R N f : MvPolynomial (Fin N) R).IsHomogeneous d := by
  have he : (rho R N f : MvPolynomial (Fin N) R) =
      aeval (fun i : ℕ+ => esymm (Fin N) R i) (polynomialEquiv R f) := by
    exact (Subalgebra.mvPolynomial_aeval_coe _ _ _).symm
  rw [he]
  exact weightedHomogeneous_aeval hf _ (fun i => isHomogeneous_esymm _ _ _)

/-- A homogeneous component of a symmetric polynomial is symmetric. -/
def symmetricComponent (N d : ℕ) (p : symmetricSubalgebra (Fin N) R) :
    symmetricSubalgebra (Fin N) R :=
  ⟨MvPolynomial.homogeneousComponent d p.val, fun perm => by
    rw [MvPolynomial.rename_homogeneousComponent, p.property perm]⟩

@[simp] theorem coe_symmetricComponent (N d : ℕ) (p : symmetricSubalgebra (Fin N) R) :
    (symmetricComponent R N d p : MvPolynomial (Fin N) R) =
      MvPolynomial.homogeneousComponent d p.val := rfl

theorem isHomogeneous_symmetricComponent (N d : ℕ) (p : symmetricSubalgebra (Fin N) R) :
    (symmetricComponent R N d p : MvPolynomial (Fin N) R).IsHomogeneous d :=
  MvPolynomial.homogeneousComponent_isHomogeneous _ _

theorem sum_symmetricComponent (N : ℕ) (p : symmetricSubalgebra (Fin N) R) :
    ∑ d ∈ Finset.range (p.val.totalDegree + 1), symmetricComponent R N d p = p := by
  apply Subtype.ext
  simpa using MvPolynomial.sum_homogeneousComponent p.val

end SymmetricFunction
