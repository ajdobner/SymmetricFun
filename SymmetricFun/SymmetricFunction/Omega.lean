module

public import SymmetricFun.SymmetricFunction.Basis.Elementary
public import SymmetricFun.SymmetricFunction.Basis.Transition.ElementaryComplete
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The omega involution

Over a commutative ring and an infinite variable type, `omega` is the graded algebra
involution exchanging elementary and complete homogeneous symmetric functions.

Using complete homogeneous evaluation from `Basis/Defs.lean`, compose with the inverse
elementary presentation. This sends `eₙ` to `hₙ`. The relation
`E(-t) H(t) = 1` implies that it also sends `hₙ` to `eₙ`, by uniqueness of inverses
in the formal power series ring. Since the elementary functions generate the algebra,
the resulting endomorphism is involutive.
-/

@[expose] public section
noncomputable section

namespace MvPowerSeries

variable (σ R : Type*)

attribute [local instance] MvPolynomial.weightedGradedAlgebra

section CommRing

variable [CommRing R] [Infinite σ]

/-- The graded endomorphism sending each positive-degree elementary generator to the
complete homogeneous function of the same degree. -/
def omegaGradedAlgHom :
    symmetricFunctionGrading σ R →ₐᵍ[R] symmetricFunctionGrading σ R :=
  (hsymmGradedAlgHom σ R).comp (esymmGradedAlgEquiv σ R).symm.toGradedAlgHom

@[simp]
theorem omegaGradedAlgHom_esymmGraded (n : ℕ) :
    omegaGradedAlgHom σ R (esymmGraded σ R n : symmetricFunctionSubalgebra σ R) =
      (hsymmGraded σ R n : symmetricFunctionSubalgebra σ R) := by
  cases n with
  | zero => simp
  | succ n =>
    change hsymmAlgHom σ R ((esymmGradedAlgEquiv σ R).symm
      (esymmGraded σ R (n + 1) : symmetricFunctionSubalgebra σ R)) = _
    exact (congrArg (hsymmAlgHom σ R)
      (esymmGradedAlgEquiv_symm_esymmGraded σ R ⟨n + 1, Nat.succ_pos n⟩)).trans
      (hsymmAlgHom_X σ R ⟨n + 1, Nat.succ_pos n⟩)

@[simp]
theorem omegaGradedAlgHom_hsymmGraded (n : ℕ) :
    omegaGradedAlgHom σ R (hsymmGraded σ R n : symmetricFunctionSubalgebra σ R) =
      (esymmGraded σ R n : symmetricFunctionSubalgebra σ R) := by
  let E : PowerSeries (symmetricFunctionSubalgebra σ R) :=
    PowerSeries.mk (fun i => (esymmGraded σ R i : symmetricFunctionSubalgebra σ R))
  let H : PowerSeries (symmetricFunctionSubalgebra σ R) :=
    PowerSeries.mk (fun i => (hsymmGraded σ R i : symmetricFunctionSubalgebra σ R))
  let f := (omegaGradedAlgHom σ R).toAlgHom.toRingHom
  have hEH : PowerSeries.rescale (-1) E * H = 1 := by
    apply PowerSeries.ext
    intro i
    simp only [PowerSeries.coeff_mul, PowerSeries.coeff_rescale, PowerSeries.coeff_mk,
      PowerSeries.coeff_one, E, H]
    apply Subtype.ext
    simpa only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, Subalgebra.coe_pow,
      Subalgebra.coe_neg, Subalgebra.coe_one, coe_esymmGraded, coe_hsymmGraded,
      Algebra.smul_def, map_pow, map_neg, map_one, mul_assoc, apply_ite,
      Subalgebra.coe_zero] using sum_antidiagonal_esymm_hsymm σ R i
  have hHE : E * PowerSeries.rescale (-1) H = 1 := by
    have h := congrArg (PowerSeries.rescale (-1 : symmetricFunctionSubalgebra σ R)) hEH
    simpa only [map_mul, PowerSeries.rescale_rescale, neg_mul_neg, one_mul,
      PowerSeries.rescale_one, RingHom.id_apply, map_one] using h
  have hfE : PowerSeries.map f E = H := by
    apply PowerSeries.ext
    intro i
    simpa only [PowerSeries.coeff_map, PowerSeries.coeff_mk, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, GradedAlgHom.coe_toAlgHom, E, H, f] using
      omegaGradedAlgHom_esymmGraded σ R i
  have hfEH : PowerSeries.rescale (-1) H * PowerSeries.map f H = 1 := by
    have h := congrArg (PowerSeries.map f) hEH
    rw [map_mul, ← PowerSeries.rescale_map, map_neg, map_one, hfE, map_one] at h
    exact h
  have h := congrArg (PowerSeries.coeff n) (left_inv_eq_right_inv hHE hfEH)
  simpa only [PowerSeries.coeff_map, PowerSeries.coeff_mk, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, GradedAlgHom.coe_toAlgHom, E, H, f] using h.symm

/-- The elementary–complete exchange squares to the identity on all symmetric functions. -/
theorem omegaGradedAlgHom_involutive : Function.Involutive (omegaGradedAlgHom σ R) := by
  have h : ((omegaGradedAlgHom σ R).toAlgHom.comp (omegaGradedAlgHom σ R).toAlgHom).comp
      (esymmAlgHom σ R) = esymmAlgHom σ R := by
    apply MvPolynomial.algHom_ext
    intro i
    change omegaGradedAlgHom σ R (omegaGradedAlgHom σ R
      (esymmAlgHom σ R (MvPolynomial.X i))) = esymmAlgHom σ R (MvPolynomial.X i)
    rw [esymmAlgHom_X, omegaGradedAlgHom_esymmGraded, omegaGradedAlgHom_hsymmGraded]
  intro f
  obtain ⟨p, rfl⟩ := (esymmAlgHom_bijective σ R).surjective f
  exact DFunLike.congr_fun h p

/-- The graded algebra involution exchanging elementary and complete homogeneous
symmetric functions. -/
def omega :
    symmetricFunctionGrading σ R ≃ₐᵍ[R] symmetricFunctionGrading σ R :=
  GradedAlgEquiv.ofBijective (omegaGradedAlgHom σ R)
    (omegaGradedAlgHom_involutive σ R).bijective

@[simp]
theorem omega_toGradedAlgHom : (omega σ R).toGradedAlgHom = omegaGradedAlgHom σ R := rfl

/-- Applying omega twice is the identity. -/
theorem omega_involutive : Function.Involutive (omega σ R) :=
  omegaGradedAlgHom_involutive σ R

@[simp]
theorem omega_omega (f : symmetricFunctionSubalgebra σ R) :
    omega σ R (omega σ R f) = f :=
  omega_involutive σ R f

@[simp]
theorem omega_symm : (omega σ R).symm = omega σ R := by
  apply GradedAlgEquiv.ext
  intro f
  apply (omega σ R).injective
  simp

@[simp]
theorem omega_esymmGraded (n : ℕ) :
    omega σ R (esymmGraded σ R n : symmetricFunctionSubalgebra σ R) =
      (hsymmGraded σ R n : symmetricFunctionSubalgebra σ R) :=
  omegaGradedAlgHom_esymmGraded σ R n

@[simp]
theorem omega_hsymmGraded (n : ℕ) :
    omega σ R (hsymmGraded σ R n : symmetricFunctionSubalgebra σ R) =
      (esymmGraded σ R n : symmetricFunctionSubalgebra σ R) :=
  omegaGradedAlgHom_hsymmGraded σ R n

/-- Omega sends an elementary partition product to the complete homogeneous product. -/
@[simp]
theorem omega_esymmPartGraded {n : ℕ} (μ : Nat.Partition n) :
    omega σ R (esymmPartGraded σ R μ : symmetricFunctionSubalgebra σ R) =
      (hsymmPartGraded σ R μ : symmetricFunctionSubalgebra σ R) := by
  change hsymmAlgHom σ R ((esymmGradedAlgEquiv σ R).symm
    (esymmPartGraded σ R μ : symmetricFunctionSubalgebra σ R)) = _
  rw [esymmGradedAlgEquiv_symm_esymmPartGraded, hsymmAlgHom_monomial, one_smul]
  exact congrArg (fun ν : IntegerPartition =>
    (hsymmPartGraded σ R ν.2 : symmetricFunctionSubalgebra σ R))
    (IntegerPartition.ofMultiplicities_multiplicities μ.toIntegerPartition)

/-- Omega sends a complete homogeneous partition product to the elementary product. -/
@[simp]
theorem omega_hsymmPartGraded {n : ℕ} (μ : Nat.Partition n) :
    omega σ R (hsymmPartGraded σ R μ : symmetricFunctionSubalgebra σ R) =
      (esymmPartGraded σ R μ : symmetricFunctionSubalgebra σ R) := by
  rw [← omega_esymmPartGraded, omega_omega]

end CommRing

end MvPowerSeries
