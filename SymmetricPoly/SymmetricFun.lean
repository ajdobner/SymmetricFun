import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.Algebra.Algebra.Subalgebra.Basic

noncomputable section

-- instance {σ : Type*} [DecidableEq σ] : DecomposableAddMonoid (σ →₀ ℕ) where
--   antidiagonal m := m.antidiagonal'.support
--   mem_antidiagonal {m} {p} := by
--     rcases p with ⟨p₁, p₂⟩
--     simp [Finsupp.antidiagonal', ← and_assoc, Multiset.toFinsupp_eq_iff,
--       ← Multiset.toFinsupp_eq_iff (f:=m)]


namespace MvPowerSeries

variable {σ : Type*} {R : Type*} [CommSemiring R]

def totalDegree (p : MvPowerSeries σ R) : ℕ∞ :=
  ⨆ (m : {m : σ →₀ ℕ // coeff m p ≠ 0}), (m.1.sum (fun _ n => n) : ℕ∞)

theorem totalDegree_C (r : R) : (C r : MvPowerSeries σ R).totalDegree = 0 := by
  sorry

theorem totalDegree_mul (p q : MvPowerSeries σ R) :
    totalDegree (p * q) ≤ totalDegree p + totalDegree q := by
  sorry

theorem totalDegree_add (p q : MvPowerSeries σ R) :
    totalDegree (p + q) ≤ max (totalDegree p) (totalDegree q) := by
  sorry

def IsBddDeg (p : MvPowerSeries σ R) : Prop := totalDegree p < ⊤

lemma isBddDeg_iff_exists_bound {σ R : Type*} [CommSemiring R] (p : MvPowerSeries σ R) :
    IsBddDeg p ↔ ∃ (D : ℕ), ∀ m, p.coeff m ≠ 0 → m.sum (fun _ e => e) ≤ D := by sorry

def bddDegSubalgebra (σ R : Type*) [CommRing R] : Subalgebra R (MvPowerSeries σ R) where
  carrier := {f | IsBddDeg f}
  algebraMap_mem' r := by
    simp [IsBddDeg, algebraMap_apply, totalDegree_C]
  add_mem' ha hb := by
    rename_i f g
    exact lt_of_le_of_lt (totalDegree_add f g) (max_lt ha hb)
  mul_mem' ha hb := by
    rename_i f g
    exact lt_of_le_of_lt (totalDegree_mul f g) (WithTop.add_lt_top.mpr ⟨ha, hb⟩)

def symmSubalgebra (σ R : Type*) [CommRing R] : Subalgebra R (MvPowerSeries σ R) where
  carrier := {f | ∀ e : Equiv.Perm σ, rename e f = f}
  algebraMap_mem' r e := rename_C e r
  mul_mem' ha hb e := by rw [map_mul, ha, hb]
  add_mem' ha hb e := by rw [map_add, ha, hb]


def symmetricFunctions (σ R : Type*) [CommRing R] : Subalgebra R (MvPowerSeries σ R) :=
  bddDegSubalgebra σ R ⊓ symmSubalgebra σ R


end MvPowerSeries
