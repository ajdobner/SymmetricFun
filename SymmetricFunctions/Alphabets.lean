import SymmetricFunctions.Plethysm.Rational
import SymmetricFunctions.Hopf.TensorSpecialization
import SymmetricFunctions.Hopf.Primitive

/-! # Coefficient-linear evaluation in independent alphabets

All outer R-coefficients are fixed. Inner polynomial variables are formal
parameters and the kth Adams substitution raises them to their kth powers.
Virtual negation instead negates every positive power-sum image. The tensor
factors describe independent alphabets, not simultaneous permutation invariants.
-/

noncomputable section

namespace SymmetricFunction

open scoped TensorProduct

variable {R : Type*} [CommRing R] [Algebra ℚ R]
variable {A : Type*} [CommRing A] [Algebra R A]

/-- Specifying the usual finite power sums recovers actual finite specialization. -/
theorem powerSumEval_psum (N : ℕ) :
    powerSumEval (fun k : ℕ+ => MvPolynomial.psum (Fin N) R k) =
      alphabetSpecialization R (Fin N) := by
  apply algHom_ext_p
  intro k
  rw [powerSumEval_p, alphabetSpecialization_fin, rho_p]

/-- Evaluate at a virtual negative alphabet. The minus sign is not a line parameter. -/
def negativeAlphabetEval (x : ℕ+ → A) : SymmetricFunction R →ₐ[R] A :=
  powerSumEval (fun k => -x k)

@[simp] theorem negativeAlphabetEval_p (x : ℕ+ → A) (k : ℕ+) :
    negativeAlphabetEval x (p (R := R) k) = -x k := powerSumEval_p _ _

/-- Scale an alphabet by a formal line parameter t. -/
def scaledAlphabetEval (t : A) (x : ℕ+ → A) : SymmetricFunction R →ₐ[R] A :=
  powerSumEval (fun k => t ^ (k : ℕ) * x k)

@[simp] theorem scaledAlphabetEval_p (t : A) (x : ℕ+ → A) (k : ℕ+) :
    scaledAlphabetEval t x (p (R := R) k) = t ^ (k : ℕ) * x k := powerSumEval_p _ _

/-- Addition of virtual alphabets adds their positive power-sum images. -/
def sumAlphabetEval (x y : ℕ+ → A) : SymmetricFunction R →ₐ[R] A :=
  powerSumEval (fun k => x k + y k)

@[simp] theorem sumAlphabetEval_p (x y : ℕ+ → A) (k : ℕ+) :
    sumAlphabetEval x y (p (R := R) k) = x k + y k := powerSumEval_p _ _

/-- Product alphabets multiply the corresponding power-sum images. -/
def productAlphabetEval (x y : ℕ+ → A) : SymmetricFunction R →ₐ[R] A :=
  powerSumEval (fun k => x k * y k)

@[simp] theorem productAlphabetEval_p (x y : ℕ+ → A) (k : ℕ+) :
    productAlphabetEval x y (p (R := R) k) = x k * y k := powerSumEval_p _ _

/-- The coefficient-linear Adams substitution on symmetric generators.
This fixes R; parameters intended to transform must be represented separately. -/
def powerSumAdams (k : ℕ+) : SymmetricFunction R →ₐ[R] SymmetricFunction R :=
  powerSumEval (fun n => p (k * n))

@[simp] theorem powerSumAdams_p (k n : ℕ+) :
    powerSumAdams (R := R) k (p n) = p (k * n) := powerSumEval_p _ _

@[simp] theorem powerSumAdams_e_one (k : ℕ+) :
    powerSumAdams (R := R) k (e 1) = p k := by
  simpa only [p_one, mul_one] using powerSumAdams_p (R := R) k 1

@[simp] theorem powerSumAdams_one :
    powerSumAdams (R := R) 1 = AlgHom.id R (SymmetricFunction R) := by
  apply algHom_ext_p
  simp

theorem powerSumAdams_comp (k l : ℕ+) :
    (powerSumAdams (R := R) k).comp (powerSumAdams l) = powerSumAdams (k * l) := by
  apply algHom_ext_p
  simp [mul_assoc]

/-- Adams substitution agrees with raising every letter of a finite alphabet to a power. -/
theorem alphabetSpecialization_powerSumAdams (N : ℕ) (k : ℕ+) (f : SymmetricFunction R) :
    alphabetSpecialization R (Fin N) (powerSumAdams k f) =
      MvPolynomial.expand (k : ℕ) (alphabetSpecialization R (Fin N) f) := by
  have he : (alphabetSpecialization R (Fin N)).comp (powerSumAdams k) =
      (MvPolynomial.expand (k : ℕ)).comp (alphabetSpecialization R (Fin N)) := by
    apply algHom_ext_p
    intro n
    simp only [AlgHom.comp_apply, powerSumAdams_p, alphabetSpecialization_fin, rho_p]
    simp [MvPolynomial.psum, pow_mul]
  exact DFunLike.congr_fun he f

/-- Coefficient-linear virtual negation is an involution. -/
theorem negativeAlphabetEval_comp_self :
    (negativeAlphabetEval (R := R) p).comp (negativeAlphabetEval p) =
      AlgHom.id R (SymmetricFunction R) := by
  apply algHom_ext_p
  simp

/-- The two power-sum blocks present the algebra of separately symmetric objects. -/
def tensorPowerSumPolynomialEquiv (R : Type*) [CommRing R] [Algebra ℚ R] :
    (SymmetricFunction R ⊗[R] SymmetricFunction R) ≃ₐ[R] MvPolynomial (ℕ+ ⊕ ℕ+) R :=
  (Algebra.TensorProduct.congr (powerSumPolynomialEquiv R).symm
    (powerSumPolynomialEquiv R).symm).trans (MvPolynomial.tensorEquivSum R ℕ+ ℕ+ R)

@[simp] theorem tensorPowerSumPolynomialEquiv_p_left (k : ℕ+) :
    tensorPowerSumPolynomialEquiv R (p k ⊗ₜ[R] 1) = MvPolynomial.X (Sum.inl k) := by
  simp [tensorPowerSumPolynomialEquiv, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]

@[simp] theorem tensorPowerSumPolynomialEquiv_p_right (k : ℕ+) :
    tensorPowerSumPolynomialEquiv R (1 ⊗ₜ[R] p k) = MvPolynomial.X (Sum.inr k) := by
  simp [tensorPowerSumPolynomialEquiv, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]

/-- Assign independent power-sum images to the two tensor factors. -/
def tensorAlphabetEval (x y : ℕ+ → A) :
    (SymmetricFunction R ⊗[R] SymmetricFunction R) →ₐ[R] A :=
  Algebra.TensorProduct.lift (powerSumEval x) (powerSumEval y) (fun _ _ => Commute.all _ _)

@[simp] theorem tensorAlphabetEval_tmul (x y : ℕ+ → A) (f g : SymmetricFunction R) :
    tensorAlphabetEval x y (f ⊗ₜ[R] g) = powerSumEval x f * powerSumEval y g := by
  simp [tensorAlphabetEval]

@[simp] theorem tensorAlphabetEval_p_left (x y : ℕ+ → A) (k : ℕ+) :
    tensorAlphabetEval x y (p (R := R) k ⊗ₜ[R] 1) = x k := by simp

@[simp] theorem tensorAlphabetEval_p_right (x y : ℕ+ → A) (k : ℕ+) :
    tensorAlphabetEval x y (1 ⊗ₜ[R] p (R := R) k) = y k := by simp

/-- Rational alphabet addition agrees with the already proved Hopf coproduct. -/
theorem tensorAlphabetEval_comp_comultiplication (x y : ℕ+ → A) :
    (tensorAlphabetEval x y).comp comultiplication = sumAlphabetEval (R := R) x y := by
  apply algHom_ext_p
  simp

/-- Independent power-sum assignments determine every map from the tensor algebra. -/
theorem tensorAlphabetEval_unique (x y : ℕ+ → A)
    (φ : (SymmetricFunction R ⊗[R] SymmetricFunction R) →ₐ[R] A)
    (hx : ∀ k, φ (p k ⊗ₜ[R] 1) = x k) (hy : ∀ k, φ (1 ⊗ₜ[R] p k) = y k) :
    φ = tensorAlphabetEval x y := by
  apply Algebra.TensorProduct.ext
  · apply algHom_ext_p
    intro k
    simpa using hx k
  · apply algHom_ext_p
    intro k
    simpa using hy k

/-- Ordinary polynomial parameters together with one symmetric alphabet.
For finite σ this is the mixed finite-polynomial/symmetric object. -/
abbrev MixedAlphabet (σ R : Type*) [CommRing R] :=
  MvPolynomial σ R ⊗[R] SymmetricFunction R

/-- Independent ordinary variables and power-sum variables present mixed objects. -/
def mixedPowerSumPolynomialEquiv (σ R : Type*) [CommRing R] [Algebra ℚ R] :
    MixedAlphabet σ R ≃ₐ[R] MvPolynomial (σ ⊕ ℕ+) R :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl)
    (powerSumPolynomialEquiv R).symm).trans (MvPolynomial.tensorEquivSum R σ ℕ+ R)

variable {σ : Type*}

@[simp] theorem mixedPowerSumPolynomialEquiv_X (i : σ) :
    mixedPowerSumPolynomialEquiv σ R (MvPolynomial.X i ⊗ₜ[R] 1) =
      MvPolynomial.X (Sum.inl i) := by
  simp [mixedPowerSumPolynomialEquiv, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]

@[simp] theorem mixedPowerSumPolynomialEquiv_p (k : ℕ+) :
    mixedPowerSumPolynomialEquiv σ R (1 ⊗ₜ[R] p k) = MvPolynomial.X (Sum.inr k) := by
  simp [mixedPowerSumPolynomialEquiv, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]

/-- Simultaneously evaluate ordinary parameters and the independent symmetric factor. -/
def mixedAlphabetEval (z : σ → A) (x : ℕ+ → A) : MixedAlphabet σ R →ₐ[R] A :=
  Algebra.TensorProduct.lift (MvPolynomial.aeval z) (powerSumEval x)
    (fun _ _ => Commute.all _ _)

@[simp] theorem mixedAlphabetEval_tmul (z : σ → A) (x : ℕ+ → A)
    (q : MvPolynomial σ R) (f : SymmetricFunction R) :
    mixedAlphabetEval (R := R) z x (q ⊗ₜ[R] f) = MvPolynomial.aeval z q * powerSumEval x f := by
  simp [mixedAlphabetEval]

@[simp] theorem mixedAlphabetEval_X (z : σ → A) (x : ℕ+ → A) (i : σ) :
    mixedAlphabetEval (R := R) z x
      (MvPolynomial.X i ⊗ₜ[R] (1 : SymmetricFunction R)) = z i := by simp

@[simp] theorem mixedAlphabetEval_p (z : σ → A) (x : ℕ+ → A) (k : ℕ+) :
    mixedAlphabetEval (R := R) z x ((1 : MvPolynomial σ R) ⊗ₜ[R] p k) = x k := by simp

/-- Parameter images and symmetric power-sum images uniquely determine mixed evaluation. -/
theorem mixedAlphabetEval_unique (z : σ → A) (x : ℕ+ → A)
    (φ : MixedAlphabet σ R →ₐ[R] A)
    (hz : ∀ i, φ (MvPolynomial.X i ⊗ₜ[R] 1) = z i)
    (hx : ∀ k, φ (1 ⊗ₜ[R] p k) = x k) : φ = mixedAlphabetEval z x := by
  apply Algebra.TensorProduct.ext
  · apply MvPolynomial.algHom_ext
    intro i
    simpa using hz i
  · apply algHom_ext_p
    intro k
    simpa using hx k

/-- Adams substitution on INNER parameters and symmetric generators; R remains fixed. -/
def mixedAdams (k : ℕ+) : MixedAlphabet σ R →ₐ[R] MixedAlphabet σ R :=
  Algebra.TensorProduct.map (MvPolynomial.expand (k : ℕ)) (powerSumAdams k)

@[simp] theorem mixedAdams_tmul (k : ℕ+) (q : MvPolynomial σ R) (f : SymmetricFunction R) :
    mixedAdams (σ := σ) (R := R) k (q ⊗ₜ[R] f) =
      MvPolynomial.expand (k : ℕ) q ⊗ₜ[R] powerSumAdams k f := by
  simp [mixedAdams, Algebra.TensorProduct.map_tmul]

@[simp] theorem mixedAdams_X (k : ℕ+) (i : σ) :
    mixedAdams (σ := σ) (R := R) k (MvPolynomial.X i ⊗ₜ[R] (1 : SymmetricFunction R)) =
      (MvPolynomial.X i ^ (k : ℕ)) ⊗ₜ[R] (1 : SymmetricFunction R) := by simp

@[simp] theorem mixedAdams_p (k n : ℕ+) :
    mixedAdams (σ := σ) (R := R) k ((1 : MvPolynomial σ R) ⊗ₜ[R] p n) =
      (1 : MvPolynomial σ R) ⊗ₜ[R] p (k * n) := by simp

@[simp] theorem mixedAdams_one :
    mixedAdams (σ := σ) (R := R) 1 = AlgHom.id R (MixedAlphabet σ R) := by
  apply Algebra.TensorProduct.ext
  · apply MvPolynomial.algHom_ext
    intro i
    simp
  · apply algHom_ext_p
    intro k
    simp

/-- Adams substitutions compose multiplicatively in their positive indices. -/
theorem mixedAdams_comp (k l : ℕ+) :
    (mixedAdams (σ := σ) (R := R) k).comp (mixedAdams l) = mixedAdams (k * l) := by
  apply Algebra.TensorProduct.ext
  · apply MvPolynomial.algHom_ext
    intro i
    simp [pow_mul]
  · apply algHom_ext_p
    intro n
    simp [mul_assoc]

/-- Coefficient-linear plethystic evaluation at a mixed inner expression.
This is distinct from the integral universal lambda morphism `lambdaEval`. -/
def mixedPlethysticEval (g : MixedAlphabet σ R) : SymmetricFunction R →ₐ[R] MixedAlphabet σ R :=
  powerSumEval (fun k => mixedAdams (σ := σ) (R := R) k g)

@[simp] theorem mixedPlethysticEval_p (g : MixedAlphabet σ R) (k : ℕ+) :
    mixedPlethysticEval g (p k) = mixedAdams (σ := σ) (R := R) k g := powerSumEval_p _ _

@[simp] theorem mixedPlethysticEval_e_one (g : MixedAlphabet σ R) :
    mixedPlethysticEval g (e 1) = g := by
  simp [mixedPlethysticEval]

/-- Evaluation at X/(1-t). Every positive-index denominator must be a unit.
No infinite series is formed: a symmetric function is a finite polynomial in p. -/
def geometricAlphabetEval (t : A) (h : ∀ k : ℕ+, IsUnit (1 - t ^ (k : ℕ)))
    (x : ℕ+ → A) : SymmetricFunction R →ₐ[R] A :=
  powerSumEval (fun k => x k * ↑((h k).unit⁻¹))

@[simp] theorem geometricAlphabetEval_p (t : A)
    (h : ∀ k : ℕ+, IsUnit (1 - t ^ (k : ℕ))) (x : ℕ+ → A) (k : ℕ+) :
    geometricAlphabetEval t h x (p (R := R) k) = x k * ↑((h k).unit⁻¹) :=
  powerSumEval_p _ _

/-- In a field the same unit-based evaluator has the familiar quotient formula. -/
theorem geometricAlphabetEval_p_field {K : Type*} [Field K] [Algebra R K]
    (t : K) (h : ∀ k : ℕ+, IsUnit (1 - t ^ (k : ℕ))) (x : ℕ+ → K) (k : ℕ+) :
    geometricAlphabetEval t h x (p (R := R) k) = x k / (1 - t ^ (k : ℕ)) := by
  rw [geometricAlphabetEval_p, Units.val_inv_eq_inv_val, (h k).unit_spec, div_eq_mul_inv]

/-- The defining denominator equation, valid even in rings with zero divisors. -/
theorem geometricAlphabetEval_denominator (t : A)
    (h : ∀ k : ℕ+, IsUnit (1 - t ^ (k : ℕ))) (x : ℕ+ → A) (k : ℕ+) :
    geometricAlphabetEval t h x (p (R := R) k) * (1 - t ^ (k : ℕ)) = x k := by
  rw [geometricAlphabetEval_p]
  simpa only [(h k).unit_spec] using (Units.inv_mul_cancel_right (x k) (h k).unit)

/-- The denominator equations uniquely determine evaluation, independent of unit choices. -/
theorem geometricAlphabetEval_unique (t : A)
    (h : ∀ k : ℕ+, IsUnit (1 - t ^ (k : ℕ))) (x : ℕ+ → A)
    (φ : SymmetricFunction R →ₐ[R] A)
    (hφ : ∀ k : ℕ+, φ (p k) * (1 - t ^ (k : ℕ)) = x k) :
    φ = geometricAlphabetEval t h x := by
  apply algHom_ext_p
  intro k
  apply (h k).mul_right_cancel
  exact (hφ k).trans (geometricAlphabetEval_denominator t h x k).symm

end SymmetricFunction
