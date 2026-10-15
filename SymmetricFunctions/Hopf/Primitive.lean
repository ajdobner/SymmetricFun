import SymmetricFunctions.Hopf.Series

/-! # Integral primitivity of the positive Newton power sums -/

namespace SymmetricFunction

noncomputable section

open scoped TensorProduct

variable {R : Type*} [CommRing R]

/-- Newton's recurrence in convolution form, with strictly positive power-sum indices. -/
theorem newton_convolution (n : ℕ) :
    ∑ ij ∈ Finset.antidiagonal n,
      (-1 : R)^ij.1 • (e (R := R) ij.1 * p (Nat.succPNat ij.2)) =
        ((-1 : R)^(n + 2) * (n + 1 : ℕ)) • e (n + 1) := by
  let F : ℕ × ℕ → SymmetricFunction R := fun ij =>
    (-1 : R)^ij.1 • (e ij.1 * p (Nat.succPNat ij.2))
  have ht : ∑ ij ∈ (newtonPairs (n + 1)).attach,
      (-1 : R)^ij.val.1 • (e ij.val.1 * p (newtonRight ij)) =
      ∑ ij ∈ (Finset.antidiagonal n).erase (0, n), F ij := by
    apply Finset.sum_bij (fun ij _ => (ij.val.1, ij.val.2 - 1))
    · intro ij _
      have hp := newtonPairs_spec ij.property
      simp only [Finset.mem_erase, Finset.mem_antidiagonal]
      constructor
      · intro heq
        have hz := congrArg Prod.fst heq
        change ij.val.1 = 0 at hz
        omega
      · omega
    · intro a _ b _ hab
      apply Subtype.ext
      have ha := newtonPairs_spec a.property
      have hb := newtonPairs_spec b.property
      simp only [Prod.mk.injEq] at hab
      apply Prod.ext <;> omega
    · intro b hb
      have hb' := Finset.mem_erase.mp hb
      have hs := Finset.mem_antidiagonal.mp hb'.2
      have hpos : 0 < b.1 := by
        by_contra h
        have : b = (0, n) := Prod.ext (by omega) (by omega)
        exact hb'.1 this
      refine ⟨⟨(b.1, b.2 + 1), ?_⟩, Finset.mem_attach _ _, ?_⟩
      · simp only [newtonPairs, Finset.mem_filter, Finset.mem_antidiagonal]
        exact ⟨by omega, hpos, by omega⟩
      · simp
    · intro ij _
      have hp := newtonPairs_spec ij.property
      have hi : newtonRight ij = (Nat.succPNat (ij.val.2 - 1)) := by
        apply PNat.coe_injective
        change ij.val.2 = ij.val.2 - 1 + 1
        omega
      simp only [F, hi]
  have he := Finset.add_sum_erase (Finset.antidiagonal n) F
    (show (0, n) ∈ Finset.antidiagonal n by simp)
  have hn := p_rec (R := R) ((Nat.succPNat n) : ℕ+)
  simp only [Nat.succPNat_coe, Nat.succ_eq_add_one] at hn
  rw [ht] at hn
  have hF : F (0, n) = p (Nat.succPNat n) := by simp [F]
  rw [hF] at he
  change (∑ ij ∈ Finset.antidiagonal n, F ij) = _
  rw [← he, hn]
  exact sub_add_cancel _ _

/-- The coefficient of u^n is p_(n+1); there is no cardinal-valued p_0. -/
def powerSumGeneratingSeries : PowerSeries (SymmetricFunction R) :=
  PowerSeries.mk (fun n => p (Nat.succPNat n))

@[simp] theorem coeff_powerSumGeneratingSeries (n : ℕ) :
    PowerSeries.coeff n (powerSumGeneratingSeries (R := R)) = p (Nat.succPNat n) :=
  PowerSeries.coeff_mk _ _

/-- The integral logarithmic-derivative identity, before using the inverse series. -/
theorem elementary_powerSum_series :
    PowerSeries.rescale (-1) (elementaryGeneratingSeries (R := R)) *
        powerSumGeneratingSeries =
      - PowerSeries.derivative
        (PowerSeries.rescale (-1) elementaryGeneratingSeries) := by
  ext n
  simp only [PowerSeries.coeff_mul, PowerSeries.coeff_rescale,
    coeff_elementaryGeneratingSeries, coeff_powerSumGeneratingSeries,
    map_neg, PowerSeries.coeff_derivative]
  have hn := newton_convolution (R := R) n
  simp only [Algebra.smul_def, map_mul, map_pow, map_neg, map_one, map_natCast,
    mul_assoc] at hn
  simp only [mul_assoc]
  rw [hn]
  simp only [pow_succ, Nat.cast_add, Nat.cast_one]
  ring

/-- An integral expression for the positive power-sum series. -/
theorem powerSum_series_eq :
    powerSumGeneratingSeries (R := R) =
      - PowerSeries.derivative (PowerSeries.rescale (-1) elementaryGeneratingSeries) *
        completeGeneratingSeries := by
  calc
    _ = (PowerSeries.rescale (-1) elementaryGeneratingSeries * completeGeneratingSeries) *
        powerSumGeneratingSeries := by rw [elementary_complete_series, one_mul]
    _ = (PowerSeries.rescale (-1) elementaryGeneratingSeries * powerSumGeneratingSeries) *
        completeGeneratingSeries := by ring
    _ = _ := by rw [elementary_powerSum_series]

private theorem map_series_derivative {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (F : PowerSeries A) :
    PowerSeries.map φ (PowerSeries.derivative F) =
      PowerSeries.derivative (PowerSeries.map φ F) := by
  ext n
  simp [PowerSeries.coeff_derivative]

/-- Alphabet addition adds the integral positive power-sum generating series. -/
theorem comultiplication_powerSumSeries :
    PowerSeries.map comultiplication.toRingHom (powerSumGeneratingSeries (R := R)) =
      PowerSeries.map (Algebra.TensorProduct.includeLeft :
        SymmetricFunction R →ₐ[R] SymmetricFunction R ⊗[R] SymmetricFunction R).toRingHom
        powerSumGeneratingSeries +
      PowerSeries.map (Algebra.TensorProduct.includeRight :
        SymmetricFunction R →ₐ[R] SymmetricFunction R ⊗[R] SymmetricFunction R).toRingHom
        powerSumGeneratingSeries := by
  let φ := (Algebra.TensorProduct.includeLeft :
    SymmetricFunction R →ₐ[R] SymmetricFunction R ⊗[R] SymmetricFunction R).toRingHom
  let ψ := (Algebra.TensorProduct.includeRight :
    SymmetricFunction R →ₐ[R] SymmetricFunction R ⊗[R] SymmetricFunction R).toRingHom
  let L := PowerSeries.map φ
  let Q := PowerSeries.map ψ
  let M := PowerSeries.map (comultiplication (R := R)).toRingHom
  let G := PowerSeries.rescale (-1) (elementaryGeneratingSeries (R := R))
  let H := completeGeneratingSeries (R := R)
  let P := powerSumGeneratingSeries (R := R)
  have hp (f : SymmetricFunction R →+*
      SymmetricFunction R ⊗[R] SymmetricFunction R) :
      PowerSeries.map f P =
        - PowerSeries.derivative (PowerSeries.map f G) * PowerSeries.map f H := by
    simpa only [map_mul, map_neg, map_series_derivative] using
      congrArg (PowerSeries.map f) (powerSum_series_eq (R := R))
  have hl : L G * L H = 1 := by
    simpa only [map_mul, map_one] using congrArg L (elementary_complete_series (R := R))
  have hr : Q G * Q H = 1 := by
    simpa only [map_mul, map_one] using congrArg Q (elementary_complete_series (R := R))
  have hg : M G = L G * Q G := by
    have hm (f : SymmetricFunction R →+*
        SymmetricFunction R ⊗[R] SymmetricFunction R) :
        PowerSeries.map f G =
          PowerSeries.rescale (-1) (PowerSeries.map f elementaryGeneratingSeries) := by
      simpa [G] using (PowerSeries.rescale_map f (-1) elementaryGeneratingSeries).symm
    rw [hm, comultiplication_elementarySeries, map_mul, ← hm φ, ← hm ψ]
  have hh : M H = L H * Q H := comultiplication_completeSeries
  change M P = L P + Q P
  rw [hp, hg, hh, hp φ, hp ψ, Derivation.leibniz]
  change -(L G * PowerSeries.derivative (Q G) + Q G * PowerSeries.derivative (L G)) *
      (L H * Q H) = _
  calc
    _ = (- PowerSeries.derivative (L G) * L H) * (Q G * Q H) +
        (- PowerSeries.derivative (Q G) * Q H) * (L G * L H) := by ring
    _ = _ := by rw [hl, hr]; ring

/-- Every positive power sum is primitive, over any commutative coefficient ring. -/
@[simp] theorem comultiplication_p (k : ℕ+) :
    comultiplication (p (R := R) k) = p k ⊗ₜ[R] 1 + 1 ⊗ₜ[R] p k := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero k.ne_zero
  have hk : k = Nat.succPNat n := PNat.coe_injective hn
  rw [hk]
  have hc := congrArg (PowerSeries.coeff n) (comultiplication_powerSumSeries (R := R))
  simpa using hc

end

end SymmetricFunction
