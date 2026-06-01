import SymmetricPoly.DecomposableAddMonoid
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Antidiagonal

noncomputable section

instance {σ : Type*} [DecidableEq σ] : DecomposableAddMonoid (σ →₀ ℕ) where
  antidiagonal m := m.antidiagonal'.support
  mem_antidiagonal {m} {p} := by
    rcases p with ⟨p₁, p₂⟩
    simp [Finsupp.antidiagonal', ← and_assoc, Multiset.toFinsupp_eq_iff,
      ← Multiset.toFinsupp_eq_iff (f:=m)]


-- namespace MvPowerSeries

-- def IsBddDeg [CommSemiring R] (f : MvPowerSeries σ R) : Prop :=
--   ∃ d : ℕ, ∀ m : σ →₀ ℕ, f.coeff m ≠ 0 → m.sum (fun _ n => n) ≤ d

-- def boundedSubalgebra (σ R : Type*) [CommSemiring R] : Subalgebra R
--   (MvPowerSeries σ R) where
--   carrier := {f | IsBddDeg f}


-- end MvPowerSeries
