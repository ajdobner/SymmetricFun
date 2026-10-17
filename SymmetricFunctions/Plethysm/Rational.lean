import SymmetricFunctions.Plethysm.Adams
import SymmetricFunctions.Grading.Evaluation

/-! # The power-sum polynomial presentation over a rational algebra

Division occurs only in the inverse Newton substitution and only under
`Algebra ℚ R`. The resulting equivalence is an algebra equivalence; no
polynomial line-element lambda structure is transported along it.
-/

noncomputable section

namespace SymmetricFunction

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The positive left index of an internal Newton term. -/
def newtonLeft {n : ℕ} (ij : {ij : ℕ × ℕ // ij ∈ newtonPairs n}) : ℕ+ :=
  ⟨ij.val.1, (newtonPairs_spec ij.property).2.1⟩

@[simp] theorem coe_newtonLeft {n : ℕ} (ij : {ij : ℕ × ℕ // ij ∈ newtonPairs n}) :
    (newtonLeft ij : ℕ) = ij.val.1 := rfl

theorem newtonLeft_lt {n : ℕ} (ij : {ij : ℕ × ℕ // ij ∈ newtonPairs n}) :
    (newtonLeft ij : ℕ) < n := (newtonPairs_spec ij.property).2.2

/-- The reciprocal of the signed leading coefficient in the kth Newton identity. -/
def inverseNewtonCoefficient (k : ℕ+) : R :=
  algebraMap ℚ R (((-1 : ℚ)^((k : ℕ)+1) * (k : ℕ))⁻¹)

theorem newtonCoefficient_mul_inverse (k : ℕ+) :
    ((-1 : R)^((k : ℕ)+1) * (k : ℕ)) * inverseNewtonCoefficient (R := R) k = 1 := by
  have hz : ((-1 : ℚ)^((k : ℕ)+1) * (k : ℕ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast k.pos.ne')
  rw [inverseNewtonCoefficient,
    show (-1 : R)^((k : ℕ)+1) * (k : ℕ) =
      algebraMap ℚ R ((-1 : ℚ)^((k : ℕ)+1) * (k : ℕ)) by simp,
    ← map_mul, mul_inv_cancel₀ hz, map_one]

/-- Inverse elementary coordinates, with e_i serving as the formal coordinate variables.
Applying the power-sum substitution turns these expressions into elementary functions. -/
def elementaryPowerCoordinates (k : ℕ+) : SymmetricFunction R :=
  inverseNewtonCoefficient (R := R) k • (e k + ∑ ij ∈ (newtonPairs k).attach,
    (-1 : R)^ij.val.1 • (elementaryPowerCoordinates (newtonLeft ij) * e (newtonRight ij)))
termination_by (k : ℕ)
decreasing_by exact newtonLeft_lt ij

theorem elementaryPowerCoordinates_rec (k : ℕ+) :
    elementaryPowerCoordinates (R := R) k =
      inverseNewtonCoefficient (R := R) k • (e k + ∑ ij ∈ (newtonPairs k).attach,
        (-1 : R)^ij.val.1 • (elementaryPowerCoordinates (newtonLeft ij) * e (newtonRight ij))) := by
  rw [elementaryPowerCoordinates]

/-- Send each positive elementary generator to the matching power sum, as an algebra map. -/
def powerSumSubstitution : SymmetricFunction R →ₐ[R] SymmetricFunction R := eval p

/-- The inverse algebra substitution prescribed by divided Newton identities. -/
def inversePowerSumSubstitution : SymmetricFunction R →ₐ[R] SymmetricFunction R :=
  eval elementaryPowerCoordinates

omit [Algebra ℚ R] in
@[simp] theorem powerSumSubstitution_e (k : ℕ+) :
    powerSumSubstitution (e (R := R) k) = p k := eval_e _ k

@[simp] theorem inversePowerSumSubstitution_e (k : ℕ+) :
    inversePowerSumSubstitution (e (R := R) k) = elementaryPowerCoordinates k := eval_e _ k

/-- The first inverse law, proved from the original integral Newton recurrence. -/
theorem powerSumSubstitution_elementaryPowerCoordinates (k : ℕ+) :
    powerSumSubstitution (elementaryPowerCoordinates (R := R) k) = e k := by
  induction k using PNat.strongInductionOn with
  | _ k ih =>
    rw [elementaryPowerCoordinates_rec, map_smul, map_add, powerSumSubstitution_e, map_sum]
    have hleft (ij : {ij : ℕ × ℕ // ij ∈ newtonPairs k}) :
        powerSumSubstitution (elementaryPowerCoordinates (R := R) (newtonLeft ij)) = e ij.val.1 :=
      ih (newtonLeft ij) (newtonLeft_lt ij)
    simp only [map_smul, map_mul, powerSumSubstitution_e, hleft]
    rw [p_rec, sub_add_cancel, smul_smul, mul_comm,
      newtonCoefficient_mul_inverse, one_smul]

/-- The second inverse law, with no assumption of algebraic independence. -/
@[simp] theorem inversePowerSumSubstitution_p (k : ℕ+) :
    inversePowerSumSubstitution (p (R := R) k) = e k := by
  induction k using PNat.strongInductionOn with
  | _ k ih =>
    rw [p_rec, map_sub, map_smul, inversePowerSumSubstitution_e, map_sum]
    have he : ∀ ij ∈ (newtonPairs (k : ℕ)).attach,
        inversePowerSumSubstitution (R := R)
          ((-1 : R)^ij.val.1 • (e ij.val.1 * p (newtonRight ij))) =
        (-1 : R)^ij.val.1 • (elementaryPowerCoordinates (newtonLeft ij) * e (newtonRight ij)) := by
      intro ij _
      rw [map_smul, map_mul, ih (newtonRight ij) (newtonRight_lt ij)]
      rw [show ij.val.1 = (newtonLeft ij : ℕ) from rfl, inversePowerSumSubstitution_e]
    rw [Finset.sum_congr rfl he, elementaryPowerCoordinates_rec,
      smul_smul, newtonCoefficient_mul_inverse, one_smul, add_sub_cancel_right]

/-- The proved invertible change from elementary generators to power sums. -/
def powerSumChangeOfGenerators (R : Type*) [CommRing R] [Algebra ℚ R] :
    SymmetricFunction R ≃ₐ[R] SymmetricFunction R :=
  AlgEquiv.ofAlgHom powerSumSubstitution inversePowerSumSubstitution
    (by
      apply algHom_ext
      intro k
      simp only [AlgHom.comp_apply, AlgHom.id_apply, inversePowerSumSubstitution_e,
        powerSumSubstitution_elementaryPowerCoordinates])
    (by
      apply algHom_ext
      intro k
      simp only [AlgHom.comp_apply, AlgHom.id_apply, powerSumSubstitution_e,
        inversePowerSumSubstitution_p])

/-- Polynomial freeness of the positive power sums over a rational coefficient algebra. -/
def powerSumPolynomialEquiv (R : Type*) [CommRing R] [Algebra ℚ R] :
    MvPolynomial ℕ+ R ≃ₐ[R] SymmetricFunction R :=
  (polynomialEquiv R).symm.trans (powerSumChangeOfGenerators R)

@[simp] theorem powerSumPolynomialEquiv_X (k : ℕ+) :
    powerSumPolynomialEquiv R (MvPolynomial.X k) = p k := by
  change powerSumSubstitution ((polynomialEquiv R).symm (MvPolynomial.X k)) = p k
  rw [polynomialEquiv_symm_X, powerSumSubstitution_e]


@[simp] theorem powerSumPolynomialEquiv_symm_p (k : ℕ+) :
    (powerSumPolynomialEquiv R).symm (p k) = MvPolynomial.X k := by
  apply (powerSumPolynomialEquiv R).injective
  simp

@[simp] theorem powerSumChangeOfGenerators_e (k : ℕ+) :
    powerSumChangeOfGenerators R (e k) = p k := powerSumSubstitution_e k

@[simp] theorem powerSumChangeOfGenerators_symm_p (k : ℕ+) :
    (powerSumChangeOfGenerators R).symm (p k) = e k := inversePowerSumSubstitution_p k

/-- The inverse coordinates have the correct weighted degree. -/
theorem isHomogeneous_elementaryPowerCoordinates (k : ℕ+) :
    IsHomogeneous (elementaryPowerCoordinates (R := R) k) k := by
  induction k using PNat.strongInductionOn with
  | _ k ih =>
    rw [elementaryPowerCoordinates_rec]
    apply IsHomogeneous.smul
    apply (homogeneousSubmodule R k).add_mem (isHomogeneous_e k)
    apply (homogeneousSubmodule R k).sum_mem
    intro ij _
    have hg := ((ih (newtonLeft ij) (newtonLeft_lt ij)).mul
      (isHomogeneous_e (R := R) (newtonRight ij))).smul ((-1 : R)^ij.val.1)
    change IsHomogeneous _ (k : ℕ)
    simpa only [coe_newtonLeft, coe_newtonRight, (newtonPairs_spec ij.property).1] using hg

/-- Both directions of the change of generators preserve weighted degree. -/
theorem IsHomogeneous.powerSumChange {f : SymmetricFunction R} {d : ℕ}
    (hf : IsHomogeneous f d) : IsHomogeneous (powerSumChangeOfGenerators R f) d :=
  isHomogeneous_eval p isHomogeneous_p hf

theorem IsHomogeneous.inversePowerSumChange {f : SymmetricFunction R} {d : ℕ}
    (hf : IsHomogeneous f d) : IsHomogeneous ((powerSumChangeOfGenerators R).symm f) d :=
  isHomogeneous_eval elementaryPowerCoordinates isHomogeneous_elementaryPowerCoordinates hf

/-- Restriction of the proved change of generators to one homogeneous degree. -/
def powerSumHomogeneous (R : Type*) [CommRing R] [Algebra ℚ R] (d : ℕ) :
    homogeneousSubmodule R d ≃ₗ[R] homogeneousSubmodule R d where
  toFun f := ⟨powerSumChangeOfGenerators R f, IsHomogeneous.powerSumChange f.property⟩
  invFun f := ⟨(powerSumChangeOfGenerators R).symm f,
    IsHomogeneous.inversePowerSumChange f.property⟩
  left_inv f := Subtype.ext ((powerSumChangeOfGenerators R).symm_apply_apply f)
  right_inv f := Subtype.ext ((powerSumChangeOfGenerators R).apply_symm_apply f)
  map_add' f g := Subtype.ext (map_add (powerSumChangeOfGenerators R) (f : SymmetricFunction R) g)
  map_smul' r f := Subtype.ext (map_smul (powerSumChangeOfGenerators R) r (f : SymmetricFunction R))

@[simp] theorem powerSumHomogeneous_apply (d : ℕ) (f : homogeneousSubmodule R d) :
    (powerSumHomogeneous R d f : SymmetricFunction R) = powerSumChangeOfGenerators R f := rfl

@[simp] theorem powerSumHomogeneous_symm_apply (d : ℕ) (f : homogeneousSubmodule R d) :
    ((powerSumHomogeneous R d).symm f : SymmetricFunction R) =
      (powerSumChangeOfGenerators R).symm f := rfl

variable {A : Type*} [CommRing A] [Algebra R A]

/-- Coefficient-linear evaluation from specified positive power-sum images.
Outer R-coefficients are fixed; no lambda structure on A is required. -/
def powerSumEval (x : ℕ+ → A) : SymmetricFunction R →ₐ[R] A :=
  (MvPolynomial.aeval x).comp (powerSumPolynomialEquiv R).symm.toAlgHom

@[simp] theorem powerSumEval_p (x : ℕ+ → A) (k : ℕ+) :
    powerSumEval x (p (R := R) k) = x k := by simp [powerSumEval]

@[simp] theorem powerSumEval_e_one (x : ℕ+ → A) :
    powerSumEval x (e (R := R) 1) = x 1 := by
  simpa only [p_one] using powerSumEval_p (R := R) x 1

@[simp] theorem powerSumEval_algebraMap (x : ℕ+ → A) (r : R) :
    powerSumEval x (algebraMap R (SymmetricFunction R) r) = algebraMap R A r :=
  (powerSumEval x).commutes r

/-- Power sums determine every coefficient-algebra map when the coefficients contain Q. -/
theorem algHom_ext_p {f g : SymmetricFunction R →ₐ[R] A}
    (hp : ∀ k : ℕ+, f (p k) = g (p k)) : f = g := by
  have he : f.comp (powerSumPolynomialEquiv R).toAlgHom =
      g.comp (powerSumPolynomialEquiv R).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro k
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, powerSumPolynomialEquiv_X] using hp k
  apply DFunLike.ext
  intro x
  obtain ⟨q, rfl⟩ := (powerSumPolynomialEquiv R).surjective x
  exact DFunLike.congr_fun he q

theorem powerSumEval_unique (φ : SymmetricFunction R →ₐ[R] A) :
    powerSumEval (fun k => φ (p k)) = φ := by
  apply algHom_ext_p
  simp

/-- The universal R-algebra evaluation property of the rational power-sum presentation. -/
def powerSumEvalEquiv : (ℕ+ → A) ≃ (SymmetricFunction R →ₐ[R] A) where
  toFun := powerSumEval
  invFun φ k := φ (p k)
  left_inv x := funext (powerSumEval_p x)
  right_inv := powerSumEval_unique

@[simp] theorem powerSumEval_self :
    powerSumEval (fun k => p (R := R) k) = AlgHom.id R (SymmetricFunction R) :=
  powerSumEval_unique (AlgHom.id R (SymmetricFunction R))

theorem comp_powerSumEval {B : Type*} [CommRing B] [Algebra R B]
    (φ : A →ₐ[R] B) (x : ℕ+ → A) :
    φ.comp (powerSumEval x) = powerSumEval (fun k => φ (x k)) := by
  apply algHom_ext_p
  simp

end SymmetricFunction
