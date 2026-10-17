import SymmetricFunctions.Basis.Elementary
import SymmetricFunctions.Omega

/-! # Complete partition bases and polynomial freeness -/

namespace SymmetricFunction

noncomputable section

open SymmetricFunctions

variable {R : Type*} [CommRing R] {d : ℕ}

/-- The product of complete functions indexed by the parts of a partition. -/
def hPart (μ : Nat.Partition d) : SymmetricFunction R := (μ.parts.map h).prod

theorem hPart_eq_prod (μ : Nat.Partition d) :
    hPart (R := R) μ = (Partition.toExponents μ).prod (fun i k => h i ^ k) :=
  Partition.prod_parts μ h

@[simp] theorem omega_ePart (μ : Nat.Partition d) : omega (ePart (R := R) μ) = hPart μ := by
  simp [ePart, hPart, map_multiset_prod, Multiset.map_map]

@[simp] theorem omega_hPart (μ : Nat.Partition d) : omega (hPart (R := R) μ) = ePart μ := by
  rw [← omega_ePart, omega_omega]

theorem isHomogeneous_hPart (μ : Nat.Partition d) : IsHomogeneous (hPart (R := R) μ) d := by
  rw [← omega_ePart]
  exact (isHomogeneous_ePart μ).omega

@[simp] theorem hPart_zero (μ : Nat.Partition 0) : hPart (R := R) μ = 1 := by
  simp [hPart]

theorem hPart_mul {m n : ℕ} (μ : Nat.Partition m) (ν : Nat.Partition n) :
    hPart (R := R) μ * hPart ν = hPart (Partition.union μ ν) := by
  simp [hPart]

/-- The complete basis of a homogeneous piece. -/
def hBasis (R : Type*) [CommRing R] (d : ℕ) :
    Module.Basis (Nat.Partition d) R (homogeneousSubmodule R d) :=
  (eBasis R d).map (omegaHomogeneous d)

@[simp] theorem hBasis_apply (μ : Nat.Partition d) :
    (hBasis R d μ : SymmetricFunction R) = hPart μ := by
  simp [hBasis]

theorem hBasis_repr (f : homogeneousSubmodule R d) (μ : Nat.Partition d) :
    (hBasis R d).repr f μ = (polynomialEquiv R (omega f)).coeff (Partition.toExponents μ) := by
  change (eBasis R d).repr (omegaHomogeneous d f) μ = _
  rw [eBasis_repr, omegaHomogeneous_apply]

/-- The complete basis of the full ring, with finite expansions. -/
def hBasisAll (R : Type*) [CommRing R] :
    Module.Basis (Σ d, Nat.Partition d) R (SymmetricFunction R) :=
  (eBasisAll R).map omega.toLinearEquiv

@[simp] theorem hBasisAll_apply (μ : Σ d, Nat.Partition d) :
    hBasisAll R μ = hPart μ.2 := by
  simp [hBasisAll]

theorem hBasisAll_repr (f : SymmetricFunction R) (μ : Σ d, Nat.Partition d) :
    (hBasisAll R).repr f μ =
      (polynomialEquiv R (omega f)).coeff (Partition.toExponents μ.2) := by
  change (eBasisAll R).repr (omega f) μ = _
  exact eBasisAll_repr _ _

/-- The polynomial presentation in the positive complete generators. -/
def completePolynomialEquiv (R : Type*) [CommRing R] :
    SymmetricFunction R ≃ₐ[R] MvPolynomial ℕ+ R :=
  omega.trans (polynomialEquiv R)

@[simp] theorem completePolynomialEquiv_h (i : ℕ+) :
    completePolynomialEquiv R (h i) = MvPolynomial.X i := by
  simp [completePolynomialEquiv]

@[simp] theorem completePolynomialEquiv_symm_X (i : ℕ+) :
    (completePolynomialEquiv R).symm (MvPolynomial.X i) = h i := by
  apply (completePolynomialEquiv R).injective
  simp

variable {A : Type*} [CommSemiring A] [Algebra R A]

/-- Algebra maps are determined by the positive complete generators. -/
theorem algHom_ext_h {f g : SymmetricFunction R →ₐ[R] A}
    (hh : ∀ i : ℕ+, f (h i) = g (h i)) : f = g := by
  have he : f.comp omega.toAlgHom = g.comp omega.toAlgHom := by
    apply algHom_ext
    intro i
    simpa using hh i
  apply DFunLike.ext
  intro z
  have hz := DFunLike.congr_fun he (omega z)
  simpa using hz

/-- Evaluate by assigning arbitrary images to the positive complete generators. -/
def completeEval (x : ℕ+ → A) : SymmetricFunction R →ₐ[R] A :=
  (eval x).comp omega.toAlgHom

@[simp] theorem completeEval_h (x : ℕ+ → A) (i : ℕ+) :
    completeEval x (h (R := R) i) = x i := by simp [completeEval]

@[simp] theorem completeEval_h_zero (x : ℕ+ → A) : completeEval x (h (R := R) 0) = 1 := by
  simp

theorem completeEval_unique (f : SymmetricFunction R →ₐ[R] A) :
    completeEval (fun i : ℕ+ => f (h i)) = f := by
  apply algHom_ext_h
  simp

/-- Polynomial freeness of the complete generators as a universal evaluator. -/
def completeEvalEquiv : (ℕ+ → A) ≃ (SymmetricFunction R →ₐ[R] A) where
  toFun := completeEval
  invFun f i := f (h i)
  left_inv x := funext (completeEval_h x)
  right_inv := completeEval_unique

theorem completeEval_hPart (x : ℕ+ → A) (μ : Nat.Partition d) :
    completeEval x (hPart (R := R) μ) =
      (Partition.toExponents μ).prod (fun i k => x i ^ k) := by
  simp [hPart_eq_prod, Finsupp.prod]

theorem completeEval_hBasisAll (x : ℕ+ → A) (μ : Σ d, Nat.Partition d) :
    completeEval x (hBasisAll R μ) =
      (Partition.toExponents μ.2).prod (fun i k => x i ^ k) := by
  rw [hBasisAll_apply, completeEval_hPart]

section Examples

attribute [local irreducible] SymmetricFunction

example : hBasisAll R ⟨0, default⟩ = 1 := by simp

example : hBasisAll R ⟨2, Nat.Partition.indiscrete 2⟩ = e 1 ^ 2 - e 2 := by
  simp [hPart, h_two]

example (x : ℕ+ → A) : completeEval x (h (R := R) 1 ^ 2) = x 1 ^ 2 := by
  rw [map_pow]
  exact congrArg (fun a => a ^ 2) (completeEval_h x 1)

end Examples

end

end SymmetricFunction
