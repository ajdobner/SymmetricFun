import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.Algebra.GradedMonoid
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Multiset.Antidiagonal
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.DirectSum.Internal

namespace MvPowerSeries

variable {σ R : Type*} [CommSemiring R]


theorem isHomogeneous_monomial {d : σ →₀ ℕ} (r : R) {n : ℕ} (hn : d.degree = n) :
    IsHomogeneous (monomial d r) n := by
  rw [Finsupp.degree_eq_weight_one] at hn
  classical
  intro c hc
  rw [coeff_monomial] at hc
  split_ifs at hc with h
  · subst c
    exact hn
  · contradiction

theorem isHomogeneous_C (r : R) :
    IsHomogeneous (C r : MvPowerSeries σ R) 0 := isHomogeneous_monomial r (map_zero _)

theorem isHomogeneous_one : IsHomogeneous (1 : MvPowerSeries σ R) 0 := isHomogeneous_C 1

theorem isHomogeneous_zero (n : ℕ) : IsHomogeneous (0 : MvPowerSeries σ R) n := by
  intro c hc
  contradiction


variable (σ R)

/-- The submodule of homogeneous `MvPowerSeries`s of degree `n`. -/
def homogeneousSubmodule (n : ℕ) : Submodule R (MvPowerSeries σ R) where
  carrier := { x | x.IsHomogeneous n }
  smul_mem' r a ha c hc := by
    rw [coeff_smul] at hc
    apply ha
    intro h
    apply hc
    rw [h]
    exact smul_zero r
  zero_mem' := isHomogeneous_zero n
  add_mem' {a b} ha hb c hc := by
    rw [map_add] at hc
    obtain h | h : coeff c a ≠ 0 ∨ coeff c b ≠ 0 := by
      contrapose! hc
      simp only [hc, add_zero]
    · exact ha h
    · exact hb h

@[simp]
theorem mem_homogeneousSubmodule (n : ℕ) (p : MvPowerSeries σ R) :
    p ∈ homogeneousSubmodule σ R n ↔ p.IsHomogeneous n := Iff.rfl

variable {σ R}

theorem homogeneousSubmodule_mul (m n : ℕ) :
  homogeneousSubmodule σ R m * homogeneousSubmodule σ R n ≤ homogeneousSubmodule σ R (m + n) := by
  classical
  rw [Submodule.mul_le]
  intro φ hφ ψ hψ c hc
  rw [coeff_mul] at hc
  obtain ⟨⟨d, e⟩, hde, H⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  have aux : coeff d φ ≠ 0 ∧ coeff e ψ ≠ 0 := by
    contrapose! H
    by_cases h : coeff d φ = 0 <;>
      simp_all only [Ne, not_false_iff, zero_mul, mul_zero]
  rw [← Finset.mem_antidiagonal.mp hde, ← hφ aux.1, ← hψ aux.2, map_add]

instance HomogeneousSubmodule.gradedMonoid :
  SetLike.GradedMonoid (homogeneousSubmodule σ R) where
  one_mem := isHomogeneous_one
  mul_mem _ _ _ _ := IsHomogeneous.mul

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

@[simp]
theorem mem_boundedDegreeSubalgebra {x : MvPowerSeries σ R} :
    x ∈ boundedDegreeSubalgebra σ R ↔ HasBoundedDegree x := by
  sorry



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
