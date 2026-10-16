import SymmetricFunctions.Realization.SeriesBasic
import SymmetricFunctions.PowerSum

/-! # Bounded symmetric functions as symmetric multivariate series -/

noncomputable section

namespace SymmetricFunction

open SymmetricFunctions SymmetricFunctions.Series

variable (R : Type*) [CommRing R]

/-- Extend the actual monomial orbit series linearly along the proved monomial basis. -/
def seriesLinear : SymmetricFunction R →ₗ[R] MvPowerSeries ℕ R :=
  (mBasisAll R).constr R (fun μ => monomialSeries μ.2)

@[simp] theorem seriesLinear_basis (μ : Σ d, Nat.Partition d) :
    seriesLinear R (mBasisAll R μ) = monomialSeries μ.2 :=
  (mBasisAll R).constr_basis R _ μ

@[simp] theorem seriesLinear_mPart {d : ℕ} (μ : Nat.Partition d) :
    seriesLinear R (mPart μ) = monomialSeries μ := by
  simpa only [mBasisAll_apply] using seriesLinear_basis R ⟨d, μ⟩

/-- Finite polynomial specialization followed by the natural series inclusion. -/
def finiteSeries (N : ℕ) : SymmetricFunction R →ₐ[R] MvPowerSeries (Fin N) R :=
  (MvPolynomial.coeToMvPowerSeries.algHom R).comp
    ((MvPolynomial.symmetricSubalgebra (Fin N) R).val.comp (rho R N))

@[simp] theorem finiteSeries_apply (N : ℕ) (f : SymmetricFunction R) :
    finiteSeries R N f = ((rho R N f).val : MvPowerSeries (Fin N) R) := by
  simp [finiteSeries]

/-- The series map recovers every finite specialization, including empty and small alphabets. -/
@[simp] theorem finiteRestriction_seriesLinear (N : ℕ) (f : SymmetricFunction R) :
    finiteRestriction R N (seriesLinear R f) = finiteSeries R N f := by
  have he : (finiteRestriction R N).toLinearMap.comp (seriesLinear R) =
      (finiteSeries R N).toLinearMap := by
    apply (mBasisAll R).ext
    intro μ
    change finiteRestriction R N (seriesLinear R (mBasisAll R μ)) = _
    simp
  exact DFunLike.congr_fun he f

/-- The bounded series realization as an algebra map, proved via finite restrictions. -/
def toSeries : SymmetricFunction R →ₐ[R] MvPowerSeries ℕ R where
  __ := seriesLinear R
  map_zero' := (seriesLinear R).map_zero
  map_one' := by
    apply eq_of_finiteRestriction_eq
    intro N
    simp
  map_mul' f g := by
    apply eq_of_finiteRestriction_eq
    intro N
    simp
  commutes' r := by
    apply eq_of_finiteRestriction_eq
    intro N
    change finiteRestriction R N (seriesLinear R (algebraMap R (SymmetricFunction R) r)) = _
    rw [finiteRestriction_seriesLinear]
    rw [AlgHom.commutes, AlgHom.commutes]

@[simp] theorem toSeries_mPart {d : ℕ} (μ : Nat.Partition d) :
    toSeries R (mPart μ) = monomialSeries μ := seriesLinear_mPart R μ

@[simp] theorem finiteRestriction_toSeries (N : ℕ) (f : SymmetricFunction R) :
    finiteRestriction R N (toSeries R f) = ((rho R N f).val : MvPowerSeries (Fin N) R) := by
  exact (finiteRestriction_seriesLinear R N f).trans (finiteSeries_apply R N f)

theorem toSeries_injective : Function.Injective (toSeries R) := by
  intro f g hfg
  apply (stableEquiv R).injective
  apply Subtype.ext
  funext N
  apply Subtype.ext
  apply MvPolynomial.coe_injective (Fin N) R
  simpa only [stableEquiv_apply, finiteRestriction_toSeries] using
    congrArg (finiteRestriction R N) hfg

/-- Coefficients are precisely the corresponding full monomial-basis coordinates. -/
theorem coeff_toSeries (f : SymmetricFunction R) (a : ℕ →₀ ℕ) :
    MvPowerSeries.coeff a (toSeries R f) = (mBasisAll R).repr f (exponentPartition a) := by
  classical
  change MvPowerSeries.coeff a (seriesLinear R f) = _
  rw [seriesLinear, Module.Basis.constr_apply]
  simp only [Finsupp.sum, map_sum, MvPowerSeries.coeff_smul, coeff_monomialSeries,
    ← exponentPartition_eq_iff, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm

theorem isSymmetric_toSeries (f : SymmetricFunction R) : IsSymmetric (toSeries R f) :=
  isSymmetric_of_coeff_eq _ fun a b hab => by
    rw [coeff_toSeries, coeff_toSeries, exponentPartition_eq_of_parts_eq a b hab]

theorem hasBoundedTotalDegree_toSeries (f : SymmetricFunction R) :
    HasBoundedTotalDegree (toSeries R f) := by
  classical
  refine ⟨((mBasisAll R).repr f).support.sup Sigma.fst, fun a ha => ?_⟩
  rw [coeff_toSeries] at ha
  change (exponentPartition a).1 ≤ _
  exact Finset.le_sup (f := fun μ : Σ d, Nat.Partition d => μ.1)
    (Finsupp.mem_support_iff.mpr ha)

/-- The map into the proof-irrelevant bounded symmetric subalgebra. -/
def boundedSeriesMap : SymmetricFunction R →ₐ[R] BoundedSymmetricSeries R :=
  (toSeries R).codRestrict (boundedSymmetricSubalgebra R)
    (fun f => ⟨isSymmetric_toSeries R f, hasBoundedTotalDegree_toSeries R f⟩)

/-- Bounded symmetry leaves only finitely many partition coefficients to reconstruct. -/
theorem boundedSeriesMap_surjective : Function.Surjective (boundedSeriesMap R) := by
  classical
  intro F
  obtain ⟨D, hD⟩ := F.property.2
  let s : Finset (Σ d, Nat.Partition d) := (Finset.range (D + 1)).sigma (fun _ => Finset.univ)
  let c : (Σ d, Nat.Partition d) →₀ R := Finsupp.onFinset s
    (fun μ => MvPowerSeries.coeff (representative μ) F.val) (by
      intro μ hμ
      have hd := hD (representative μ) hμ
      simpa [s, Nat.lt_succ_iff] using hd)
  refine ⟨(mBasisAll R).repr.symm c, ?_⟩
  apply Subtype.ext
  apply MvPowerSeries.ext
  intro a
  change MvPowerSeries.coeff a (toSeries R ((mBasisAll R).repr.symm c)) = _
  rw [coeff_toSeries, LinearEquiv.apply_symm_apply]
  change MvPowerSeries.coeff (representative (exponentPartition a)) F.val = _
  exact F.property.1.coeff_eq (by simp)

/-- The polynomial-backed bounded ring is exactly the uniformly bounded symmetric series. -/
def boundedSeriesEquiv : SymmetricFunction R ≃ₐ[R] BoundedSymmetricSeries R :=
  AlgEquiv.ofBijective (boundedSeriesMap R)
    ⟨fun _ _ h => toSeries_injective R (congrArg Subtype.val h), boundedSeriesMap_surjective R⟩

@[simp] theorem boundedSeriesEquiv_apply (f : SymmetricFunction R) :
    (boundedSeriesEquiv R f).val = toSeries R f := rfl

@[simp] theorem toSeries_boundedSeriesEquiv_symm (f : BoundedSymmetricSeries R) :
    toSeries R ((boundedSeriesEquiv R).symm f) = f.val :=
  congrArg Subtype.val ((boundedSeriesEquiv R).apply_symm_apply f)

/-- The series realization uses total alphabet degree, corresponding to weighted SF degree. -/
theorem isHomogeneous_toSeries {f : SymmetricFunction R} {d : ℕ} (hf : IsHomogeneous f d) :
    (toSeries R f).IsHomogeneous d := by
  intro a ha
  change Finsupp.weight (fun _ : ℕ => (1 : ℕ)) a = d
  rw [← Finsupp.degree_eq_weight_one]
  obtain ⟨N, b, rfl⟩ := exists_fin_exponent a
  have hc : (rho R N f).val.coeff b ≠ 0 := by
    simpa only [← coeff_finiteRestriction, finiteRestriction_toSeries,
      MvPolynomial.coeff_coe] using ha
  have hd := isHomogeneous_rho R N d f hf hc
  have he : (b.embDomain Fin.valEmbedding).degree = b.degree :=
    congrArg Multiset.sum (exponentParts_embDomain Fin.valEmbedding b)
  rw [he]
  change Finsupp.weight (fun _ : Fin N => (1 : ℕ)) b = d at hd
  simpa only [← Finsupp.degree_eq_weight_one] using hd

/-- Homogeneous projection commutes with the two realizations. -/
theorem toSeries_homogeneousComponent (d : ℕ) (f : SymmetricFunction R) :
    toSeries R (homogeneousComponent d f) =
      MvPowerSeries.homogeneousComponent d (toSeries R f) := by
  have he : (toSeries R).toLinearMap.comp (homogeneousComponent d) =
      (MvPowerSeries.homogeneousComponent d).comp (toSeries R).toLinearMap := by
    apply (mBasisAll R).ext
    intro μ
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [mBasisAll_apply]
    by_cases hμ : μ.1 = d
    · subst d
      rw [homogeneousComponent_of_mem (isHomogeneous_mPart μ.2)]
      exact (MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent.mp
        (isHomogeneous_toSeries R (isHomogeneous_mPart μ.2)))
    · rw [homogeneousComponent_of_mem_ne (isHomogeneous_mPart μ.2) hμ, map_zero]
      apply MvPowerSeries.ext
      intro a
      rw [map_zero, MvPowerSeries.coeff_homogeneousComponent]
      split_ifs with ha
      · symm
        exact MvPowerSeries.IsHomogeneous.coeff_eq_zero
          (isHomogeneous_toSeries R (isHomogeneous_mPart μ.2))
          (fun he => hμ (he.symm.trans ha))
      · rfl
  exact DFunLike.congr_fun he f

/-- Elementary functions restrict to the usual finite elementary polynomials. -/
@[simp] theorem finiteRestriction_toSeries_e (N n : ℕ) :
    finiteRestriction R N (toSeries R (e n)) =
      (MvPolynomial.esymm (Fin N) R n : MvPowerSeries (Fin N) R) := by
  rw [finiteRestriction_toSeries, rho_e]

/-- Complete functions restrict to the usual finite complete polynomials. -/
@[simp] theorem finiteRestriction_toSeries_h (N n : ℕ) :
    finiteRestriction R N (toSeries R (h n)) =
      (MvPolynomial.hsymm (Fin N) R n : MvPowerSeries (Fin N) R) := by
  rw [finiteRestriction_toSeries, rho_h]

/-- Monomial functions have the actual coefficient-one orbit formula in the infinite alphabet. -/
theorem coeff_toSeries_mPart {d : ℕ} (μ : Nat.Partition d) (a : ℕ →₀ ℕ) :
    MvPowerSeries.coeff a (toSeries R (mPart μ)) =
      if exponentParts a = μ.parts then 1 else 0 := by
  rw [toSeries_mPart, coeff_monomialSeries]

end SymmetricFunction
