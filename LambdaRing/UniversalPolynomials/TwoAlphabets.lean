import LambdaRing.UniversalPolynomials.Bounds
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Elementary substitution in one block of a disjoint polynomial alphabet -/

namespace LambdaRing.UniversalPolynomial

noncomputable section

open MvPolynomial

variable (R : Type*) [CommRing R]

/-- Coefficients of the iterated polynomial become the right alphabet. -/
@[simp] theorem sumAlgEquiv_symm_C (σ τ : Type*) (q : MvPolynomial τ R) :
    (sumAlgEquiv R σ τ).symm (C q) = rename Sum.inr q := by
  apply (sumAlgEquiv R σ τ).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (DFunLike.congr_fun (sumAlgEquiv_comp_rename_inr R σ τ) q).symm

/-- Renaming only the left block commutes with the iterated polynomial presentation. -/
theorem sumAlgEquiv_rename_left {σ υ τ : Type*} (f : σ → υ)
    (q : MvPolynomial (σ ⊕ τ) R) :
    sumAlgEquiv R υ τ (rename (Sum.map f id) q) =
      rename f (sumAlgEquiv R σ τ q) := by
  have he : (sumAlgEquiv R υ τ).toAlgHom.comp (rename (Sum.map f id)) =
      ((rename f).restrictScalars R).comp (sumAlgEquiv R σ τ).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i <;> simp
  exact DFunLike.congr_fun he q

/-- Elementary substitution in the left finite block, fixing the entire right block. -/
def leftElementary (N : ℕ) (τ : Type*) :
    MvPolynomial (Fin N ⊕ τ) R →ₐ[R] MvPolynomial (Fin N ⊕ τ) R :=
  aeval (Sum.elim (fun i : Fin N => rename Sum.inl (esymm (Fin N) R (i.val + 1)))
    (fun j : τ => X (Sum.inr j)))

/-- In the iterated presentation, left substitution is the ordinary finite elementary map. -/
theorem sumAlgEquiv_leftElementary (N : ℕ) (τ : Type*) (q : MvPolynomial (Fin N ⊕ τ) R) :
    sumAlgEquiv R (Fin N) τ (leftElementary R N τ q) =
      aeval (fun i : Fin N => esymm (Fin N) (MvPolynomial τ R) (i.val + 1))
        (sumAlgEquiv R (Fin N) τ q) := by
  let E := aeval (R := MvPolynomial τ R)
    (fun i : Fin N => esymm (Fin N) (MvPolynomial τ R) (i.val + 1))
  have he : (sumAlgEquiv R (Fin N) τ).toAlgHom.comp (leftElementary R N τ) =
      (E.restrictScalars R).comp (sumAlgEquiv R (Fin N) τ).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | inl i =>
      simp only [AlgHom.comp_apply, leftElementary, aeval_X, Sum.elim_inl,
        AlgEquiv.coe_toAlgHom, sumAlgEquiv_X_inl, AlgHom.restrictScalars_apply, E]
      have hc := DFunLike.congr_fun (sumAlgEquiv_comp_rename_inl R (Fin N) τ)
        (esymm (Fin N) R (i.val + 1))
      simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, mapAlgHom_apply,
        Algebra.ofId_apply, map_esymm] using hc
    | inr j =>
      simp [leftElementary, E]
  exact DFunLike.congr_fun he q

/-- The finite fundamental theorem remains injective with an arbitrary right coefficient block. -/
theorem leftElementary_injective (N : ℕ) (τ : Type*) :
    Function.Injective (leftElementary R N τ) := by
  intro p q hpq
  apply (sumAlgEquiv R (Fin N) τ).injective
  have he := congrArg (sumAlgEquiv R (Fin N) τ) hpq
  simp only [sumAlgEquiv_leftElementary] at he
  have hi := (SymmetricFunction.finitePresentation (MvPolynomial τ R) N).injective
  apply hi
  apply Subtype.ext
  simpa only [SymmetricFunction.finitePresentation_apply] using he

/-- An additive change of weights transports weighted homogeneity. -/
theorem weightedHomogeneous_mapWeight {σ M D : Type*} [AddCommMonoid M] [AddCommMonoid D]
    (ψ : M →+ D) {w : σ → M} {q : MvPolynomial σ R} {d : M}
    (hq : q.IsWeightedHomogeneous w d) :
    q.IsWeightedHomogeneous (fun i => ψ (w i)) (ψ d) := by
  intro a ha
  have he := congrArg ψ (hq ha)
  simpa only [Finsupp.weight_apply, Finsupp.sum, map_sum, map_nsmul] using he

/-- Renaming preserves any assigned weights that agree on the renamed variables. -/
theorem weightedHomogeneous_rename {σ τ M : Type*} [AddCommMonoid M]
    (f : σ → τ) {w : σ → M} {v : τ → M} (hw : ∀ i, v (f i) = w i)
    {q : MvPolynomial σ R} {d : M} (hq : q.IsWeightedHomogeneous w d) :
    (rename f q).IsWeightedHomogeneous v d := by
  rw [rename_eq_aeval]
  apply SymmetricFunctions.weightedHomogeneous_aeval hq
  intro i
  simpa only [Function.comp_apply, hw i] using isWeightedHomogeneous_X R v (f i)

/-- Elementary polynomials have weight n times the common weight of their alphabet entries. -/
theorem weightedHomogeneous_rename_esymm {σ τ M : Type*} [Fintype σ] [AddCommMonoid M]
    (f : σ → τ) (w : τ → M) (v : M) (hw : ∀ i, w (f i) = v) (n : ℕ) :
    (rename f (esymm σ R n)).IsWeightedHomogeneous w (n • v) := by
  classical
  simp only [esymm, map_sum, map_prod, rename_X]
  apply (weightedHomogeneousSubmodule R w (n • v)).sum_mem
  intro t ht
  have hp := IsWeightedHomogeneous.prod t (fun i => X (R := R) (f i)) (fun _ => v)
    (fun i _ => by simpa only [hw i] using isWeightedHomogeneous_X R w (f i))
  rw [Finset.sum_const, (Finset.mem_powersetCard.mp ht).2] at hp
  exact hp

/-- Left elementary substitution preserves and reflects all compatible block weights. -/
theorem leftElementary_weighted_iff {M : Type*} [AddCommMonoid M]
    (N : ℕ) (τ : Type*) (v : M) (w : τ → M) (q : MvPolynomial (Fin N ⊕ τ) R) (d : M) :
    (leftElementary R N τ q).IsWeightedHomogeneous (Sum.elim (fun _ => v) w) d ↔
      q.IsWeightedHomogeneous (Sum.elim (fun i : Fin N => (i.val + 1) • v) w) d := by
  apply SymmetricFunctions.weightedHomogeneous_aeval_iff
  · intro i
    cases i with
    | inl i => exact weightedHomogeneous_rename_esymm R Sum.inl _ v (fun _ => rfl) (i.val + 1)
    | inr j => exact isWeightedHomogeneous_X R _ (Sum.inr j)
  · exact leftElementary_injective R N τ

end

end LambdaRing.UniversalPolynomial
