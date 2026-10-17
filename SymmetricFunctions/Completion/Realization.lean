import SymmetricFunctions.Completion.Basic

/-! # The degree completion as symmetric multivariate power series

Each exponent reads just one homogeneous component. Multiplication is verified
at finite truncations, so no unsupported infinite sum is involved.
-/
noncomputable section
namespace SymmetricFunction
open SymmetricFunctions SymmetricFunctions.Series
variable (R : Type*) [CommRing R]
attribute [local irreducible] SymmetricFunction

/-- Assemble a completed family coefficientwise in the actual alphabet variables. -/
def completionSeriesFamily (F : DegreeCompletion R) : MvPowerSeries ℕ R :=
  fun a => MvPowerSeries.coeff a (toSeries R (DegreeCompletion.component R F a.degree))

@[simp] theorem coeff_completionSeriesFamily (F : DegreeCompletion R) (a : ℕ →₀ ℕ) :
    MvPowerSeries.coeff a (completionSeriesFamily R F) =
      MvPowerSeries.coeff a (toSeries R (DegreeCompletion.component R F a.degree)) :=
  MvPowerSeries.coeff_apply (completionSeriesFamily R F) a

/-- Projecting to an exponent's own degree preserves its coefficient. -/
theorem coeff_toSeries_own_component (f : SymmetricFunction R) (a : ℕ →₀ ℕ) :
    MvPowerSeries.coeff a (toSeries R (homogeneousComponent a.degree f)) =
      MvPowerSeries.coeff a (toSeries R f) := by
  rw [toSeries_homogeneousComponent, MvPowerSeries.coeff_homogeneousComponent, ite_eq_left rfl]

@[simp] theorem completionSeriesFamily_embedding (f : SymmetricFunction R) :
    completionSeriesFamily R (completionEmbedding R f) = toSeries R f := by
  apply MvPowerSeries.ext
  intro a
  rw [coeff_completionSeriesFamily, component_completionEmbedding, coeff_toSeries_own_component]

/-- A finite truncation retains precisely coefficients below its degree cutoff. -/
theorem coeff_toSeries_truncate (D : ℕ) (F : DegreeCompletion R) (a : ℕ →₀ ℕ) :
    MvPowerSeries.coeff a (toSeries R (DegreeCompletion.truncate R D F)) =
      if a.degree ≤ D then MvPowerSeries.coeff a (completionSeriesFamily R F) else 0 := by
  rw [← coeff_toSeries_own_component, DegreeCompletion.homogeneousComponent_truncate]
  split_ifs <;> simp only [coeff_completionSeriesFamily, map_zero]

/-- Product coefficients can be computed from bounded truncations of both factors. -/
theorem coeff_completionSeriesFamily_mul (F G : DegreeCompletion R) (a : ℕ →₀ ℕ) :
    MvPowerSeries.coeff a (completionSeriesFamily R F * completionSeriesFamily R G) =
      MvPowerSeries.coeff a (toSeries R
        (DegreeCompletion.truncate R a.degree F * DegreeCompletion.truncate R a.degree G)) := by
  rw [map_mul (toSeries R), MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro bc hbc
  have hdegree : bc.1.degree + bc.2.degree = a.degree := by
    rw [← map_add, Finset.mem_antidiagonal.mp hbc]
  rw [coeff_toSeries_truncate, coeff_toSeries_truncate,
    ite_eq_left (by omega : bc.1.degree ≤ a.degree),
    ite_eq_left (by omega : bc.2.degree ≤ a.degree)]

/-- The completed alphabet realization as an algebra homomorphism. -/
def completionToSeries : DegreeCompletion R →ₐ[R] MvPowerSeries ℕ R where
  toFun := completionSeriesFamily R
  map_zero' := by
    apply MvPowerSeries.ext
    intro a
    simp only [coeff_completionSeriesFamily, DegreeCompletion.component_zero, map_zero]
  map_one' := by
    simpa only [map_one] using completionSeriesFamily_embedding R (1 : SymmetricFunction R)
  map_add' F G := by
    apply MvPowerSeries.ext
    intro a
    simp only [coeff_completionSeriesFamily, DegreeCompletion.component_add, map_add]
  map_mul' F G := by
    apply MvPowerSeries.ext
    intro a
    rw [coeff_completionSeriesFamily_mul]
    have ht := coeff_toSeries_truncate R a.degree (F * G) a
    rw [ite_eq_left le_rfl] at ht
    rw [← ht, DegreeCompletion.truncate_mul, coeff_toSeries_truncate,
      ite_eq_left le_rfl, completionSeriesFamily_embedding]
  commutes' r := by
    rw [← (completionEmbedding R).commutes, completionSeriesFamily_embedding, AlgHom.commutes]

@[simp] theorem coeff_completionToSeries (F : DegreeCompletion R) (a : ℕ →₀ ℕ) :
    MvPowerSeries.coeff a (completionToSeries R F) =
      MvPowerSeries.coeff a (toSeries R (DegreeCompletion.component R F a.degree)) :=
  coeff_completionSeriesFamily R F a

/-- Each completed homogeneous piece agrees with the series homogeneous projection. -/
theorem completionToSeries_component (F : DegreeCompletion R) (n : ℕ) :
    toSeries R (DegreeCompletion.component R F n) =
      MvPowerSeries.homogeneousComponent n (completionToSeries R F) := by
  apply MvPowerSeries.ext
  intro a
  rw [MvPowerSeries.coeff_homogeneousComponent, coeff_completionToSeries]
  by_cases ha : a.degree = n
  · simp only [ha, ite_true]
  · rw [ite_eq_right ha]
    exact MvPowerSeries.IsHomogeneous.coeff_eq_zero
      (isHomogeneous_toSeries R (DegreeCompletion.component_homogeneous R F n)) ha

theorem completionToSeries_injective : Function.Injective (completionToSeries R) := by
  intro F G h
  apply DegreeCompletion.ext
  intro n
  apply toSeries_injective R
  rw [completionToSeries_component, completionToSeries_component, h]

theorem isSymmetric_completionToSeries (F : DegreeCompletion R) :
    IsSymmetric (completionToSeries R F) := by
  apply isSymmetric_of_coeff_eq
  intro a b hab
  have hd : a.degree = b.degree := by
    exact congrArg Sigma.fst (exponentPartition_eq_of_parts_eq a b hab)
  simp only [coeff_completionToSeries, hd]
  exact (isSymmetric_toSeries R _).coeff_eq hab

/-- Homogeneity can be checked in the faithful alphabet realization. -/
theorem isHomogeneous_of_toSeries {f : SymmetricFunction R} {n : ℕ}
    (hf : (toSeries R f).IsHomogeneous n) : IsHomogeneous f n := by
  have he : homogeneousComponent n f = f := by
    apply toSeries_injective R
    rw [toSeries_homogeneousComponent]
    exact (MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent.mp hf).symm
  rw [← he]
  exact homogeneousComponent_mem n f

/-- Every homogeneous layer of a symmetric series is uniformly bounded. -/
def symmetricSeriesLayer (F : SymmetricSeries R) (n : ℕ) : BoundedSymmetricSeries R :=
  ⟨MvPowerSeries.homogeneousComponent n F.val, by
    constructor
    · apply isSymmetric_of_coeff_eq
      intro a b hab
      have hd : a.degree = b.degree :=
        congrArg Sigma.fst (exponentPartition_eq_of_parts_eq a b hab)
      rw [MvPowerSeries.coeff_homogeneousComponent,
        MvPowerSeries.coeff_homogeneousComponent, hd, F.property.coeff_eq hab]
    · refine ⟨n, fun a ha => ?_⟩
      rw [MvPowerSeries.coeff_homogeneousComponent] at ha
      split_ifs at ha with hn
      · exact hn.le
      · exact (ha rfl).elim⟩

/-- Reconstruct each bounded homogeneous layer, imposing no bound across layers. -/
def seriesCompletionFamily (F : SymmetricSeries R) : DegreeCompletion R := fun n =>
  ⟨(boundedSeriesEquiv R).symm (symmetricSeriesLayer R F n), by
    apply isHomogeneous_of_toSeries R
    rw [toSeries_boundedSeriesEquiv_symm]
    exact MvPowerSeries.isHomogeneous_homogeneousComponent F.val n⟩

@[simp] theorem component_seriesCompletionFamily (F : SymmetricSeries R) (n : ℕ) :
    DegreeCompletion.component R (seriesCompletionFamily R F) n =
      (boundedSeriesEquiv R).symm (symmetricSeriesLayer R F n) := rfl

@[simp] theorem completionToSeries_seriesCompletionFamily (F : SymmetricSeries R) :
    completionToSeries R (seriesCompletionFamily R F) = F.val := by
  apply MvPowerSeries.ext
  intro a
  rw [coeff_completionToSeries, component_seriesCompletionFamily,
    toSeries_boundedSeriesEquiv_symm]
  exact (MvPowerSeries.coeff_homogeneousComponent a.degree a F.val).trans (ite_eq_left rfl)

/-- The completed realization with its symmetry certificate. -/
def completionSymmetricSeriesMap : DegreeCompletion R →ₐ[R] SymmetricSeries R :=
  (completionToSeries R).codRestrict (symmetricSubalgebra ℕ R)
    (isSymmetric_completionToSeries R)

/-- All symmetric multivariate series, with no uniform degree bound, form the degree completion. -/
def completionSeriesEquiv : DegreeCompletion R ≃ₐ[R] SymmetricSeries R :=
  AlgEquiv.ofBijective (completionSymmetricSeriesMap R) ⟨
    fun _ _ h => completionToSeries_injective R (congrArg Subtype.val h),
    fun F => ⟨seriesCompletionFamily R F,
      Subtype.ext (completionToSeries_seriesCompletionFamily R F)⟩⟩

@[simp] theorem completionSeriesEquiv_apply (F : DegreeCompletion R) :
    (completionSeriesEquiv R F).val = completionToSeries R F := rfl

@[simp] theorem completionToSeries_embedding (f : SymmetricFunction R) :
    completionToSeries R (completionEmbedding R f) = toSeries R f :=
  completionSeriesFamily_embedding R f

/-- Finite alphabet specialization of completed functions takes values in power series. -/
def completedFiniteSpecialization (N : ℕ) :
    DegreeCompletion R →ₐ[R] MvPowerSeries (Fin N) R :=
  (finiteRestriction R N).comp (completionToSeries R)

/-- Completed specialization agrees with the original finite polynomial on bounded inputs. -/
@[simp] theorem completedFiniteSpecialization_embedding (N : ℕ) (f : SymmetricFunction R) :
    completedFiniteSpecialization R N (completionEmbedding R f) =
      ((rho R N f).val : MvPowerSeries (Fin N) R) := by
  simp only [completedFiniteSpecialization, AlgHom.comp_apply,
    completionToSeries_embedding, finiteRestriction_toSeries]

/-- A finite coefficient reads the matching total-degree component. -/
theorem coeff_completedFiniteSpecialization (N : ℕ) (F : DegreeCompletion R)
    (a : Fin N →₀ ℕ) :
    MvPowerSeries.coeff a (completedFiniteSpecialization R N F) =
      (rho R N (DegreeCompletion.component R F a.degree)).val.coeff a := by
  change MvPowerSeries.coeff a (finiteRestriction R N (completionToSeries R F)) = _
  rw [coeff_finiteRestriction, coeff_completionToSeries]
  have hd : (a.embDomain Fin.valEmbedding).degree = a.degree :=
    congrArg Multiset.sum (exponentParts_embDomain Fin.valEmbedding a)
  rw [hd, ← coeff_finiteRestriction, finiteRestriction_toSeries, MvPolynomial.coeff_coe]

end SymmetricFunction
