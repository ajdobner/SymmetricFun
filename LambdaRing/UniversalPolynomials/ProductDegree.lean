import LambdaRing.UniversalPolynomials.ProductFinite
import LambdaRing.UniversalPolynomials.TwoAlphabets

/-! # The bidegree of the universal product presentation -/

namespace LambdaRing.UniversalPolynomial

noncomputable section

open MvPolynomial

variable (R : Type*) [CommRing R]

/-- First variables have degree (1,0); second elementary generators have degree (0,j). -/
def firstAlphabetWeight (σ : Type*) : σ ⊕ ℕ+ → ℕ × ℕ :=
  Sum.elim (fun _ => (1, 0)) (fun j => (0, j))

/-- Both blocks of elementary generators carry their positive indices as weights. -/
def elementaryBlockWeight : ℕ+ ⊕ ℕ+ → ℕ × ℕ :=
  Sum.elim (fun i => (i, 0)) (fun j => (0, j))

theorem productFinite_bidegree (σ : Type*) [Fintype σ] (n : ℕ) :
    ((sumAlgEquiv R σ ℕ+).symm (productFinite R σ n)).IsWeightedHomogeneous
      (firstAlphabetWeight σ) (n, n) := by
  classical
  simp only [productFinite_eq_sum, map_sum, map_prod, map_mul, map_pow,
    sumAlgEquiv_symm_C, sumAlgEquiv_symm_X]
  apply (weightedHomogeneousSubmodule R (firstAlphabetWeight σ) (n, n)).sum_mem
  intro a ha
  have hd := (Finset.mem_finsuppAntidiag.mp ha).1
  have hx (i : σ) : IsWeightedHomogeneous (firstAlphabetWeight σ)
      (rename Sum.inr (elementaryCoefficient R (a i)) * X (Sum.inl i) ^ a i) (a i, a i) := by
    have hcoef : (elementaryCoefficient R (a i)).IsWeightedHomogeneous
        (fun j : ℕ+ => (0, (j : ℕ))) (0, a i) :=
      weightedHomogeneous_mapWeight R (AddMonoidHom.inr ℕ ℕ)
        (SymmetricFunction.isHomogeneous_e (R := R) (a i))
    have hl := weightedHomogeneous_rename R Sum.inr
      (v := firstAlphabetWeight σ) (fun _ => rfl) hcoef
    have hr := (isWeightedHomogeneous_X R (firstAlphabetWeight σ) (Sum.inl i)).pow (a i)
    simpa [firstAlphabetWeight] using hl.mul hr
  have hp := IsWeightedHomogeneous.prod Finset.univ
    (fun i : σ => rename Sum.inr (elementaryCoefficient R (a i)) * X (Sum.inl i) ^ a i)
    (fun i => (a i, a i)) (fun i _ => hx i)
  have hs : (∑ i : σ, (a i, a i)) = (n, n) := by
    apply Prod.ext <;> simp only [Prod.fst_sum, Prod.snd_sum, hd]
  rw [hs] at hp
  exact hp

/-- The finite elementary presentation in X, keeping the entire Y block as coefficients. -/
def productPresentation (N n : ℕ) : MvPolynomial (Fin N ⊕ ℕ+) R :=
  (sumAlgEquiv R (Fin N) ℕ+).symm
    ((SymmetricFunction.finitePresentation (MvPolynomial ℕ+ R) N).symm
      ⟨productFinite R (Fin N) n, productFinite_isSymmetric R (Fin N) n⟩)

@[simp] theorem leftElementary_productPresentation (N n : ℕ) :
    leftElementary R N ℕ+ (productPresentation R N n) =
      (sumAlgEquiv R (Fin N) ℕ+).symm (productFinite R (Fin N) n) := by
  apply (sumAlgEquiv R (Fin N) ℕ+).injective
  rw [sumAlgEquiv_leftElementary, AlgEquiv.apply_symm_apply]
  simp only [productPresentation, AlgEquiv.apply_symm_apply]
  have he := congrArg Subtype.val
    ((SymmetricFunction.finitePresentation (MvPolynomial ℕ+ R) N).apply_symm_apply
      ⟨productFinite R (Fin N) n, productFinite_isSymmetric R (Fin N) n⟩)
  simpa only [SymmetricFunction.finitePresentation_apply] using he

/-- Reflecting bidegree through the injective first-block elementary substitution. -/
theorem productPresentation_bidegree (N n : ℕ) :
    (productPresentation R N n).IsWeightedHomogeneous
      (Sum.elim (fun i : Fin N => (i.val + 1, 0)) (fun j : ℕ+ => (0, (j : ℕ)))) (n, n) := by
  have hh := (leftElementary_weighted_iff R N ℕ+ (1, 0) (fun j : ℕ+ => (0, (j : ℕ)))
    (productPresentation R N n) (n, n)).mp
    (by rw [leftElementary_productPresentation]; exact productFinite_bidegree R (Fin N) n)
  simpa using hh

end

end LambdaRing.UniversalPolynomial
