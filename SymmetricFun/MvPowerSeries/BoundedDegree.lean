module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.DirectSum.Internal
public import SymmetricFun.MvPowerSeries.Homogeneous

/-!
# Multivariate power series of bounded degree

The homogeneous submodules generate a subalgebra of bounded-degree series.
This algebra is internally graded by total degree, with projections given by
the homogeneous components of the underlying power series.
When the variable type is finite, this subalgebra is equivalent to the polynomial
algebra.
-/

@[expose] public section
noncomputable section

namespace MvPowerSeries

variable {σ R : Type*} [CommSemiring R]

noncomputable def boundedDegreeSubalgebra (σ R) [CommSemiring R] : Subalgebra R (MvPowerSeries σ R)
  := (DirectSum.coeAlgHom (homogeneousSubmodule σ R)).range

theorem boundedDegreeSubalgebra_toSubmodule_eq_iSup :
    (boundedDegreeSubalgebra σ R).toSubmodule = ⨆ n : ℕ, homogeneousSubmodule σ R n :=
  (Submodule.iSup_eq_toSubmodule_range (homogeneousSubmodule σ R)).symm

theorem homogeneousSubmodule_le_boundedDegreeSubalgebra (n : ℕ) :
    homogeneousSubmodule σ R n ≤ (boundedDegreeSubalgebra σ R).toSubmodule := by
  rw [boundedDegreeSubalgebra_toSubmodule_eq_iSup]
  apply le_iSup

theorem mem_boundedDegreeSubalgebra_of_isHomogeneous {n : ℕ} {x : MvPowerSeries σ R}
    (hx : x.IsHomogeneous n) : x ∈ boundedDegreeSubalgebra σ R := by
  apply homogeneousSubmodule_le_boundedDegreeSubalgebra n
  exact hx

def HasBoundedDegree (f : MvPowerSeries σ R) : Prop :=
  ∃ n : ℕ, ∀ m : σ →₀ ℕ, coeff m f ≠ 0 → m.degree ≤ n

theorem hasBoundedDegree_of_isHomogeneous (n : ℕ) {f : MvPowerSeries σ R} :
  IsHomogeneous f n → HasBoundedDegree f := by
  intro hf; use n; intro m hm
  change ∀ d, (coeff d) f ≠ 0 → (Finsupp.weight fun _ => 1) d = n at hf
  rw [← Finsupp.degree_eq_weight_one] at hf
  rw [hf m hm]

theorem HasBoundedDegree.add {f g : MvPowerSeries σ R}
    (hf : HasBoundedDegree f) (hg : HasBoundedDegree g) : HasBoundedDegree (f + g) := by
  obtain ⟨m, hm⟩ := hf
  obtain ⟨n, hn⟩ := hg
  refine ⟨max m n, fun d hd => ?_⟩
  by_cases hfd : coeff d f = 0
  · apply le_trans (hn d ?_) (le_max_right m n)
    simpa only [map_add, hfd, zero_add] using hd
  · exact le_trans (hm d hfd) (le_max_left m n)

/-- A degree bound gives a finite decomposition into homogeneous components. -/
theorem sum_homogeneousComponent_of_bound {f : MvPowerSeries σ R} {N : ℕ}
    (hf : ∀ d, coeff d f ≠ 0 → d.degree ≤ N) :
    ∑ n ∈ Finset.range (N + 1), homogeneousComponent n f = f := by
  classical
  ext d
  simp only [map_sum, coeff_homogeneousComponent, Finset.sum_ite_eq, Finset.mem_range]
  by_cases hd : d.degree < N + 1
  · simp [hd]
  · have hcoeff : coeff d f = 0 := by
      by_contra hc
      exact hd (Nat.lt_succ_of_le (hf d hc))
    simp [hcoeff]

@[simp]
theorem mem_boundedDegreeSubalgebra {x : MvPowerSeries σ R} :
    x ∈ boundedDegreeSubalgebra σ R ↔ HasBoundedDegree x := by
  constructor
  · rintro ⟨f, rfl⟩
    change HasBoundedDegree (DirectSum.coeAlgHom (homogeneousSubmodule σ R) f)
    induction f using DirectSum.induction_on with
    | zero =>
      simpa only [map_zero] using
        hasBoundedDegree_of_isHomogeneous 0 (isHomogeneous_zero (σ := σ) (R := R) 0)
    | of n f =>
      simpa only [DirectSum.coeAlgHom_of] using hasBoundedDegree_of_isHomogeneous n f.property
    | add f g hf hg =>
      simpa only [map_add] using hf.add hg
  · rintro ⟨N, hN⟩
    rw [← sum_homogeneousComponent_of_bound hN]
    exact (boundedDegreeSubalgebra σ R).sum_mem fun n _ =>
      mem_boundedDegreeSubalgebra_of_isHomogeneous (isHomogeneous_homogeneousComponent x n)

variable (σ R)

/-- The degree `n` piece of the bounded-degree power-series algebra. -/
def boundedDegreeGrading (n : ℕ) : Submodule R (boundedDegreeSubalgebra σ R) :=
  (homogeneousSubmodule σ R n).comap (boundedDegreeSubalgebra σ R).val.toLinearMap

@[simp]
theorem mem_boundedDegreeGrading (n : ℕ) (f : boundedDegreeSubalgebra σ R) :
    f ∈ boundedDegreeGrading σ R n ↔ IsHomogeneous (f : MvPowerSeries σ R) n :=
  Iff.rfl

instance BoundedDegreeGrading.gradedMonoid :
    SetLike.GradedMonoid (boundedDegreeGrading σ R) where
  one_mem := isHomogeneous_one
  mul_mem _ _ _ _ := IsHomogeneous.mul

private theorem homogeneousComponent_coeLinearMap (n : ℕ)
    (f : DirectSum ℕ fun i => boundedDegreeGrading σ R i) :
    homogeneousComponent n
        (DirectSum.coeLinearMap (boundedDegreeGrading σ R) f : MvPowerSeries σ R) =
      ((f n : boundedDegreeSubalgebra σ R) : MvPowerSeries σ R) := by
  induction f using DirectSum.induction_on with
  | zero => simp
  | of i f =>
    rw [DirectSum.coeLinearMap_of]
    by_cases h : i = n
    · subst i
      rw [DirectSum.of_eq_same]
      exact IsHomogeneous.homogeneousComponent_self f.property
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
      exact IsHomogeneous.homogeneousComponent_eq_zero f.property h
  | add f g hf hg =>
    simpa only [map_add, Subalgebra.coe_add, DirectSum.add_apply, Submodule.coe_add] using
      congrArg₂ (· + ·) hf hg

/-- Every bounded-degree power series has a unique finite homogeneous decomposition. -/
theorem boundedDegreeGrading_isInternal :
    DirectSum.IsInternal (boundedDegreeGrading σ R) := by
  classical
  change Function.Bijective (DirectSum.coeLinearMap (boundedDegreeGrading σ R))
  constructor
  · intro f g h
    ext n : 1
    apply Subtype.ext
    apply Subtype.ext
    rw [← homogeneousComponent_coeLinearMap, ← homogeneousComponent_coeLinearMap, h]
  · intro f
    obtain ⟨N, hN⟩ := mem_boundedDegreeSubalgebra.mp f.property
    let c (n : ℕ) : boundedDegreeGrading σ R n :=
      ⟨⟨homogeneousComponent n f.val, mem_boundedDegreeSubalgebra_of_isHomogeneous
        (isHomogeneous_homogeneousComponent f.val n)⟩,
        isHomogeneous_homogeneousComponent f.val n⟩
    refine ⟨∑ n ∈ Finset.range (N + 1),
      DirectSum.of (fun i => boundedDegreeGrading σ R i) n (c n), ?_⟩
    apply Subtype.ext
    simp only [map_sum, DirectSum.coeLinearMap_of, AddSubmonoidClass.coe_finsetSum]
    exact sum_homogeneousComponent_of_bound hN

instance BoundedDegreeGrading.gradedAlgebra : GradedAlgebra (boundedDegreeGrading σ R) :=
  (boundedDegreeGrading_isInternal σ R).gradedAlgebra

@[simp]
theorem coe_decompose_boundedDegreeGrading (n : ℕ) (f : boundedDegreeSubalgebra σ R) :
    ((DirectSum.decompose (boundedDegreeGrading σ R) f n :
      boundedDegreeSubalgebra σ R) : MvPowerSeries σ R) =
        homogeneousComponent n (f : MvPowerSeries σ R) := by
  rw [← homogeneousComponent_coeLinearMap]
  congr 1
  exact congrArg (fun x : boundedDegreeSubalgebra σ R => (x : MvPowerSeries σ R))
    ((DirectSum.decompose (boundedDegreeGrading σ R)).symm_apply_apply f)

/-- Grading projections agree with the homogeneous components of a power series. -/
@[simp]
theorem coe_boundedDegreeGrading_proj (n : ℕ) (f : boundedDegreeSubalgebra σ R) :
    (GradedAlgebra.proj (boundedDegreeGrading σ R) n f : MvPowerSeries σ R) =
      homogeneousComponent n (f : MvPowerSeries σ R) :=
  coe_decompose_boundedDegreeGrading σ R n f

end MvPowerSeries

namespace MvPolynomial

theorem coeToMvPowerSeries.algHom_range (σ R : Type*) [CommSemiring R] [Fintype σ] :
    (coeToMvPowerSeries.algHom R).range = MvPowerSeries.boundedDegreeSubalgebra σ R := sorry

/-- For finite types `σ` it is the case that `MvPolynomial` and `MvPowerSeries` with bounded degree
are isomorphic. -/
noncomputable def boundedDegreeAlgEquiv (σ R : Type*) [CommSemiring R] [Fintype σ] :
    MvPolynomial σ R ≃ₐ[R] MvPowerSeries.boundedDegreeSubalgebra σ R :=
  (AlgEquiv.ofInjective (coeToMvPowerSeries.algHom R) (coe_injective σ R)).trans
    (Subalgebra.equivOfEq _ _ (coeToMvPowerSeries.algHom_range σ R))

end MvPolynomial
