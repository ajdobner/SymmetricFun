import LambdaRing.UniversalPolynomials.Squarefree
import SymmetricFunctions.Stable
import LambdaRing.UniversalPolynomials.Bounds

/-! # The stable integral iteration polynomials -/

namespace LambdaRing.UniversalPolynomial

noncomputable section

open SymmetricFunction

/-- The squarefree iteration expressions form a uniformly bounded compatible family. -/
def iterationFamily (R : Type*) [CommRing R] (n m : ℕ) : BoundedStable R :=
  ⟨fun N => ⟨iterationFinite (Fin N) R n m, iterationFinite_isSymmetric R n m⟩,
    (by
      intro N
      apply Subtype.ext
      exact (coe_transition N _).trans (zeroLast_iterationFinite R N n m)),
    n * m, fun N => (iterationFinite_isHomogeneous (σ := Fin N) R n m).totalDegree_le⟩

/-- An auxiliary bounded symmetric function, constructed without any lambda operation. -/
def iterationFunction (R : Type*) [CommRing R] (n m : ℕ) : SymmetricFunction R :=
  (stableEquiv R).symm (iterationFamily R n m)

@[simp] theorem rho_iterationFunction (R : Type*) [CommRing R] (N n m : ℕ) :
    (rho R N (iterationFunction R n m) : MvPolynomial (Fin N) R) =
      iterationFinite (Fin N) R n m := by
  exact congrArg Subtype.val (rho_stableEquiv_symm R (iterationFamily R n m) N)

/-- The same lift can be computed at any alphabet at or above the degree bound. -/
theorem iterationFunction_eq_lift (R : Type*) [CommRing R] (N n m : ℕ) (hN : n * m ≤ N) :
    iterationFunction R n m =
      liftSymmetric R N ⟨iterationFinite (Fin N) R n m, iterationFinite_isSymmetric R n m⟩ :=
  stableEquiv_symm_eq_lift R (iterationFamily R n m)
    (fun K => (iterationFinite_isHomogeneous (σ := Fin K) R n m).totalDegree_le) hN

theorem iterationFunction_isHomogeneous (R : Type*) [CommRing R] (n m : ℕ) :
    IsHomogeneous (iterationFunction R n m) (n * m) := by
  rw [iterationFunction_eq_lift R (n * m) n m le_rfl]
  exact isHomogeneous_liftSymmetric R _ _ _ (iterationFinite_isHomogeneous R n m)

@[simp] theorem iterationFunction_zero (R : Type*) [CommRing R] (m : ℕ) :
    iterationFunction R 0 m = 1 := by
  apply (stableEquiv R).injective
  apply Subtype.ext
  funext N
  apply Subtype.ext
  change (rho R N (iterationFunction R 0 m) : MvPolynomial (Fin N) R) = _
  simp [rho_iterationFunction, iterationFinite]

@[simp] theorem iterationFunction_one (R : Type*) [CommRing R] (m : ℕ) :
    iterationFunction R 1 m = e m := by
  apply (stableEquiv R).injective
  apply Subtype.ext
  funext N
  apply Subtype.ext
  change (rho R N (iterationFunction R 1 m) : MvPolynomial (Fin N) R) =
    (rho R N (e m) : MvPolynomial (Fin N) R)
  rw [rho_iterationFunction, rho_e]
  simp only [iterationFinite, iterationValue_one]
  rfl

@[simp] theorem iterationFunction_one_right (R : Type*) [CommRing R] (n : ℕ) :
    iterationFunction R n 1 = e n := by
  apply (stableEquiv R).injective
  apply Subtype.ext
  funext N
  apply Subtype.ext
  change (rho R N (iterationFunction R n 1) : MvPolynomial (Fin N) R) =
    (rho R N (e n) : MvPolynomial (Fin N) R)
  rw [rho_iterationFunction, rho_e]
  simp only [iterationFinite, iterationValue_one_right]
  rfl

theorem iterationFunction_zero_right (R : Type*) [CommRing R] (n : ℕ) :
    iterationFunction R n 0 = if n ≤ 1 then 1 else 0 := by
  apply (stableEquiv R).injective
  apply Subtype.ext
  funext N
  apply Subtype.ext
  change (rho R N (iterationFunction R n 0) : MvPolynomial (Fin N) R) =
    (rho R N (if n ≤ 1 then 1 else 0) : MvPolynomial (Fin N) R)
  rw [rho_iterationFunction]
  by_cases hn : n ≤ 1 <;> simp [iterationFinite, iterationValue_zero_right, hn]

/-- The integral universal polynomial for lambda_n(lambda_m(x)), in positive variables. -/
def iterationPolynomial (n m : ℕ) : MvPolynomial ℕ+ ℤ :=
  polynomialEquiv ℤ (iterationFunction ℤ n m)

/-- Weighted degree, as opposed to ordinary degree in the elementary generators. -/
theorem iterationPolynomial_isWeightedHomogeneous (n m : ℕ) :
    (iterationPolynomial n m).IsWeightedHomogeneous (fun i : ℕ+ => (i : ℕ)) (n * m) :=
  iterationFunction_isHomogeneous ℤ n m

/-- Only the first n*m elementary generators occur in the iteration polynomial. -/
theorem iterationPolynomial_vars_le (n m : ℕ) {i : ℕ+}
    (hi : i ∈ (iterationPolynomial n m).vars) : (i : ℕ) ≤ n * m := by
  obtain ⟨a, ha, hai⟩ := (MvPolynomial.mem_vars_iff_mem_support i).mp hi
  have hw := Finsupp.le_weight_of_ne_zero' (fun i : ℕ+ => (i : ℕ))
    (Finsupp.mem_support_iff.mp hai)
  rw [iterationPolynomial_isWeightedHomogeneous n m (MvPolynomial.mem_support_iff.mp ha)] at hw
  exact hw

/-- Elementary specialization reproduces the squarefree-monomial expression in every size. -/
theorem iterationPolynomial_specialize (N n m : ℕ) :
    MvPolynomial.aeval (fun i : ℕ+ => MvPolynomial.esymm (Fin N) ℤ i)
      (iterationPolynomial n m) = iterationFinite (Fin N) ℤ n m := by
  rw [elementarySpecialization_eq_rho]
  change (rho ℤ N (iterationFunction ℤ n m) : MvPolynomial (Fin N) ℤ) = _
  exact rho_iterationFunction ℤ N n m

/-- The integral identity remains valid over every commutative coefficient ring. -/
theorem iterationPolynomial_specializeRing (R : Type*) [CommRing R] (N n m : ℕ) :
    MvPolynomial.aeval (fun i : ℕ+ => MvPolynomial.esymm (Fin N) R i)
      (iterationPolynomial n m) = iterationFinite (Fin N) R n m := by
  let φ := (MvPolynomial.map (σ := Fin N) (Int.castRingHom R)).toIntAlgHom
  have he := MvPolynomial.comp_aeval_apply
    (fun i : ℕ+ => MvPolynomial.esymm (Fin N) ℤ i) φ (iterationPolynomial n m)
  simp only [φ, RingHom.toIntAlgHom_apply, MvPolynomial.map_esymm] at he
  calc
    _ = MvPolynomial.map (Int.castRingHom R)
        (MvPolynomial.aeval (fun i : ℕ+ => MvPolynomial.esymm (Fin N) ℤ i)
          (iterationPolynomial n m)) := he.symm
    _ = _ := by rw [iterationPolynomial_specialize, map_iterationFinite]

/-- The universal iteration identity can be evaluated at arbitrary ring elements. -/
theorem iterationPolynomial_eval_fin {A : Type*} [CommRing A] (N n m : ℕ)
    (x : Fin N → A) :
    MvPolynomial.aeval (fun i : ℕ+ => elementaryValue x i) (iterationPolynomial n m) =
      iterationValue x n m := by
  let φ := MvPolynomial.aeval (R := ℤ) x
  have hc := MvPolynomial.comp_aeval_apply
    (fun i : ℕ+ => MvPolynomial.esymm (Fin N) ℤ i) φ (iterationPolynomial n m)
  have hr : φ (iterationFinite (Fin N) ℤ n m) = iterationValue x n m := by
    change φ.toRingHom (iterationValue MvPolynomial.X n m) = _
    rw [map_iterationValue]
    congr 1
    funext i
    simp [φ]
  have he := hc.symm.trans ((congrArg φ (iterationPolynomial_specialize N n m)).trans hr)
  simpa only [φ, aeval_esymm] using he

/-- Alphabet-size-independent evaluation, with no torsion restriction on the target. -/
theorem iterationPolynomial_eval {σ A : Type*} [Fintype σ] [CommRing A]
    (x : σ → A) (n m : ℕ) :
    MvPolynomial.aeval (fun i : ℕ+ => elementaryValue x i) (iterationPolynomial n m) =
      iterationValue x n m := by
  classical
  simpa only [elementaryValue_equiv, iterationValue_equiv] using
    iterationPolynomial_eval_fin (Fintype.card σ) n m (x ∘ (Fintype.equivFin σ).symm)

/-- A sufficiently large alphabet uniquely determines the bounded-variable polynomial. -/
theorem iterationPolynomial_unique (N n m : ℕ) (hN : n * m ≤ N)
    (q : MvPolynomial ℕ+ ℤ) (hq : ∀ i ∈ q.vars, (i : ℕ) ≤ n * m)
    (he : MvPolynomial.aeval (fun i : ℕ+ => MvPolynomial.esymm (Fin N) ℤ i) q =
      iterationFinite (Fin N) ℤ n m) : q = iterationPolynomial n m := by
  apply elementarySpecialization_injective_of_vars_le ℤ N
    (fun i hi => (hq i hi).trans hN)
    (fun i hi => (iterationPolynomial_vars_le n m hi).trans hN)
  rw [iterationPolynomial_specialize, he]

/-- Truncating unused elementary indices leaves the iteration polynomial unchanged. -/
theorem iterationPolynomial_truncate (N n m : ℕ) (hN : n * m ≤ N) :
    MvPolynomial.aeval (fun i : ℕ+ => if (i : ℕ) ≤ N then MvPolynomial.X i else 0)
      (iterationPolynomial n m) = iterationPolynomial n m := by
  exact MvPolynomial.aeval_ite_mem_eq_self _ (s := {i : ℕ+ | (i : ℕ) ≤ N})
    (fun _ hi => (iterationPolynomial_vars_le n m hi).trans hN)

@[simp] theorem iterationPolynomial_zero (m : ℕ) : iterationPolynomial 0 m = 1 := by
  simp [iterationPolynomial]

@[simp] theorem iterationPolynomial_one (m : ℕ+) :
    iterationPolynomial 1 m = MvPolynomial.X m := by simp [iterationPolynomial]

@[simp] theorem iterationPolynomial_one_right (n : ℕ+) :
    iterationPolynomial n 1 = MvPolynomial.X n := by simp [iterationPolynomial]

theorem iterationPolynomial_zero_right (n : ℕ) :
    iterationPolynomial n 0 = if n ≤ 1 then 1 else 0 := by
  simp [iterationPolynomial, iterationFunction_zero_right, apply_ite]

section Examples

example : iterationPolynomial 2 0 = 0 := by simp [iterationPolynomial_zero_right]

example : iterationFinite (Fin 0) ℤ 1 0 = 1 := by simp [iterationFinite]

example : iterationPolynomial 0 0 = 1 := by simp

end Examples

end

end LambdaRing.UniversalPolynomial
