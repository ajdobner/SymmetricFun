import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.PowerSeries.Substitution

/-! # Joint and iterated formal alphabets

Currying reindexes coefficients and preserves multiplication because exponent
antidiagonals split into finite products. No analytic summation is involved.
-/
noncomputable section
namespace SymmetricFunctions
variable {σ τ R : Type*} [CommRing R]

/-- Read the right exponent first and retain the left exponent as a series. -/
def sumSeriesCurry (F : MvPowerSeries (σ ⊕ τ) R) : MvPowerSeries τ (MvPowerSeries σ R) :=
  fun b a => MvPowerSeries.coeff (a.sumElim b) F

@[simp] theorem coeff_coeff_sumSeriesCurry (F : MvPowerSeries (σ ⊕ τ) R)
    (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    MvPowerSeries.coeff a (MvPowerSeries.coeff b (sumSeriesCurry F)) =
      MvPowerSeries.coeff (a.sumElim b) F := rfl

/-- Reassemble joint exponent coefficients from the two restrictions. -/
def sumSeriesUncurry (F : MvPowerSeries τ (MvPowerSeries σ R)) : MvPowerSeries (σ ⊕ τ) R :=
  fun c => MvPowerSeries.coeff (c.comapDomain Sum.inl Sum.inl_injective.injOn)
    (MvPowerSeries.coeff (c.comapDomain Sum.inr Sum.inr_injective.injOn) F)

@[simp] theorem coeff_sumSeriesUncurry (F : MvPowerSeries τ (MvPowerSeries σ R))
    (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    MvPowerSeries.coeff (a.sumElim b) (sumSeriesUncurry F) =
      MvPowerSeries.coeff a (MvPowerSeries.coeff b F) := by
  simp only [MvPowerSeries.coeff_apply, sumSeriesUncurry,
    Finsupp.comapDomain_inl_sumElim, Finsupp.comapDomain_inr_sumElim]

@[simp] theorem sumSeriesCurry_uncurry (F : MvPowerSeries τ (MvPowerSeries σ R)) :
    sumSeriesCurry (sumSeriesUncurry F) = F := by
  ext b a
  exact coeff_sumSeriesUncurry F a b

@[simp] theorem sumSeriesUncurry_curry (F : MvPowerSeries (σ ⊕ τ) R) :
    sumSeriesUncurry (sumSeriesCurry F) = F := by
  ext c
  change MvPowerSeries.coeff
    ((c.comapDomain Sum.inl _).sumElim (c.comapDomain Sum.inr _)) F = _
  rw [Finsupp.comapDomain_sumElim_comapDomain]

/-- Joint convolution is the product of the two finite exponent antidiagonals. -/
theorem sumSeriesCurry_mul (F G : MvPowerSeries (σ ⊕ τ) R) :
    sumSeriesCurry (F * G) = sumSeriesCurry F * sumSeriesCurry G := by
  classical
  ext b a
  rw [coeff_coeff_sumSeriesCurry, MvPowerSeries.coeff_mul,
    MvPowerSeries.coeff_mul, map_sum]
  simp_rw [MvPowerSeries.coeff_mul, coeff_coeff_sumSeriesCurry]
  rw [← Finsupp.image_sumElim_product_antidiagonal, Finset.sum_image]
  · rw [Finset.sum_product, Finset.sum_comm]
  · intro x _ y _ h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    apply Prod.ext <;> apply Prod.ext <;> apply Finsupp.ext
    · intro i; exact congrArg (fun c => c (Sum.inl i)) h₁
    · intro i; exact congrArg (fun c => c (Sum.inl i)) h₂
    · intro j; exact congrArg (fun c => c (Sum.inr j)) h₁
    · intro j; exact congrArg (fun c => c (Sum.inr j)) h₂

/-- The joint and iterated formal-series rings have the same coefficientwise algebra. -/
def sumSeriesEquiv : MvPowerSeries (σ ⊕ τ) R ≃ₐ[R] MvPowerSeries τ (MvPowerSeries σ R) where
  toFun := sumSeriesCurry
  invFun := sumSeriesUncurry
  left_inv := sumSeriesUncurry_curry
  right_inv := sumSeriesCurry_uncurry
  map_mul' := sumSeriesCurry_mul
  map_add' F G := by ext b a; simp
  commutes' r := by
    classical
    ext b a
    rw [coeff_coeff_sumSeriesCurry]
    have he : a.sumElim b = 0 ↔ a = 0 ∧ b = 0 := by
      constructor
      · intro h
        exact ⟨Finsupp.ext fun i => congrArg (fun c => c (Sum.inl i)) h,
          Finsupp.ext fun j => congrArg (fun c => c (Sum.inr j)) h⟩
      · rintro ⟨rfl, rfl⟩; simp
    simp only [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C, he]
    split_ifs <;> simp_all [MvPowerSeries.coeff_C]

/-- Monomials split into their two independent exponent vectors. -/
theorem sumSeriesEquiv_monomial (a : σ →₀ ℕ) (b : τ →₀ ℕ) (r : R) :
    sumSeriesEquiv (MvPowerSeries.monomial (a.sumElim b) r) =
      MvPowerSeries.monomial b (MvPowerSeries.monomial a r) := by
  classical
  ext v u
  change MvPowerSeries.coeff (u.sumElim v) (MvPowerSeries.monomial (a.sumElim b) r) = _
  have he : u.sumElim v = a.sumElim b ↔ u = a ∧ v = b := by
    constructor
    · intro h
      exact ⟨Finsupp.ext fun i => congrArg (fun c => c (Sum.inl i)) h,
        Finsupp.ext fun j => congrArg (fun c => c (Sum.inr j)) h⟩
    · rintro ⟨rfl, rfl⟩; rfl
  simp only [MvPowerSeries.coeff_monomial, he]
  split_ifs <;> simp_all [MvPowerSeries.coeff_monomial]

@[simp] theorem sumSeriesEquiv_X_inl (i : σ) :
    sumSeriesEquiv (MvPowerSeries.X (R := R) (Sum.inl i : σ ⊕ τ)) =
      MvPowerSeries.C (MvPowerSeries.X i) := by
  change sumSeriesEquiv (MvPowerSeries.monomial (Finsupp.single (Sum.inl i) 1) 1) =
    MvPowerSeries.monomial 0 (MvPowerSeries.monomial (Finsupp.single i 1) 1)
  simpa only [Finsupp.sumElim_single_zero] using
    sumSeriesEquiv_monomial (Finsupp.single i 1) (0 : τ →₀ ℕ) (1 : R)

@[simp] theorem sumSeriesEquiv_X_inr (j : τ) :
    sumSeriesEquiv (MvPowerSeries.X (R := R) (Sum.inr j : σ ⊕ τ)) =
      MvPowerSeries.X j := by
  simpa only [Finsupp.sumElim_zero_single, MvPowerSeries.X, MvPowerSeries.monomial_zero_one] using
    sumSeriesEquiv_monomial (0 : σ →₀ ℕ) (Finsupp.single j 1) (1 : R)

/-- Independent one-variable formal series have independent coefficients. -/
theorem coeff_prod_subst_X [Fintype τ] (F : τ → PowerSeries R) (b : τ →₀ ℕ) :
    MvPowerSeries.coeff b (∏ j : τ, PowerSeries.subst (MvPowerSeries.X j) (F j)) =
      ∏ j : τ, PowerSeries.coeff (b j) (F j) := by
  classical
  rw [MvPowerSeries.coeff_prod]
  simp_rw [PowerSeries.coeff_subst_single]
  let u : τ →₀ τ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun j => Finsupp.single j (b j))
  have hu : u ∈ Finset.finsuppAntidiag Finset.univ b := by
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    ext j
    simp [u]
  rw [Finset.sum_eq_single u]
  · apply Finset.prod_congr rfl
    intro j _
    simp [u]
  · intro v hv hvu
    have hn : ¬ ∀ j, v j = Finsupp.single j (v j j) := by
      intro he
      apply hvu
      have hvsum := (Finset.mem_finsuppAntidiag.mp hv).1
      have hdiag (j : τ) : v j j = b j := by
        have hh := DFunLike.congr_fun hvsum j
        rw [Finsupp.finsetSum_apply] at hh
        have hs : (∑ i : τ, v i j) = v j j := by
          calc
            _ = ∑ i : τ, if i = j then v i i else 0 := by
              apply Finset.sum_congr rfl
              intro i _
              simpa only [Finsupp.single_apply] using congrArg (fun c => c j) (he i)
            _ = _ := by simp
        exact hs.symm.trans hh
      ext j k
      change v j k = (Finsupp.single j (b j)) k
      rw [he, hdiag]
    obtain ⟨j, hj⟩ := not_forall.mp hn
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)
  · exact fun h => (h hu).elim

end SymmetricFunctions
