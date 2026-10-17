module

public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.GradedMonoid
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Multiset.Antidiagonal

/-!
# Homogeneous multivariate power series

Homogeneous series of each degree form an `R`-submodule. Multiplication adds
degrees, giving these submodules a graded monoid structure.
-/

@[expose] public section

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

@[simp]
theorem IsHomogeneous.homogeneousComponent_self {f : MvPowerSeries σ R} {n : ℕ}
    (hf : IsHomogeneous f n) : homogeneousComponent n f = f :=
  (isHomogeneous_iff_eq_homogeneousComponent.mp hf).symm

theorem IsHomogeneous.homogeneousComponent_eq_zero {f : MvPowerSeries σ R} {m n : ℕ}
    (hf : IsHomogeneous f m) (hmn : m ≠ n) : homogeneousComponent n f = 0 := by
  classical
  ext d
  rw [coeff_homogeneousComponent, map_zero]
  split_ifs with hd
  · exact hf.coeff_eq_zero (hd ▸ Ne.symm hmn)
  · rfl

@[simp]
theorem homogeneousComponent_homogeneousComponent (m n : ℕ) (f : MvPowerSeries σ R) :
    homogeneousComponent m (homogeneousComponent n f) =
      if n = m then homogeneousComponent n f else 0 := by
  classical
  split_ifs with h
  · subst m
    exact IsHomogeneous.homogeneousComponent_self (isHomogeneous_homogeneousComponent f n)
  · exact IsHomogeneous.homogeneousComponent_eq_zero (isHomogeneous_homogeneousComponent f n) h


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

end MvPowerSeries
