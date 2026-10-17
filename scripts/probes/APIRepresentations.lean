import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Algebra.TransferInstance
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace APIRepresentations

structure Wrapped (R : Type*) [CommSemiring R] where
  polynomial : MvPolynomial ℕ+ R

def wrappedEquiv (R : Type*) [CommSemiring R] : Wrapped R ≃ MvPolynomial ℕ+ R where
  toFun := Wrapped.polynomial
  invFun := Wrapped.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance (R : Type*) [CommSemiring R] : CommSemiring (Wrapped R) :=
  (wrappedEquiv R).commSemiring
instance (R : Type*) [CommRing R] : CommRing (Wrapped R) :=
  (wrappedEquiv R).commRing
instance (R : Type*) [CommSemiring R] : Algebra R (Wrapped R) :=
  (wrappedEquiv R).algebra R

def wrappedAlgEquiv (R : Type*) [CommSemiring R] : Wrapped R ≃ₐ[R] MvPolynomial ℕ+ R :=
  (wrappedEquiv R).algEquiv R

def wrappedE {R : Type*} [CommSemiring R] (i : ℕ+) : Wrapped R :=
  (wrappedAlgEquiv R).symm (MvPolynomial.X i)

example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {f g : Wrapped R →ₐ[R] A} (h : ∀ i, f (wrappedE i) = g (wrappedE i)) : f = g := by
  have h' : f.comp (wrappedAlgEquiv R).symm.toAlgHom =
      g.comp (wrappedAlgEquiv R).symm.toAlgHom := MvPolynomial.algHom_ext h
  ext p
  exact AlgHom.congr_fun h' (wrappedAlgEquiv R p)

example {R : Type*} [CommRing R] (a b : Wrapped R) :
    (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example {R : Type*} [CommRing R] (r : R) (a : Wrapped R) :
    r • a = algebraMap R (Wrapped R) r * a := Algebra.smul_def r a

def Synonym (R : Type*) [CommSemiring R] := MvPolynomial ℕ+ R
instance (R : Type*) [CommSemiring R] : CommSemiring (Synonym R) :=
  inferInstanceAs (CommSemiring (MvPolynomial ℕ+ R))
instance (R : Type*) [CommRing R] : CommRing (Synonym R) :=
  inferInstanceAs (CommRing (MvPolynomial ℕ+ R))
instance (R : Type*) [CommSemiring R] : Algebra R (Synonym R) :=
  inferInstanceAs (Algebra R (MvPolynomial ℕ+ R))

def synonymAlgEquiv (R : Type*) [CommSemiring R] : Synonym R ≃ₐ[R] MvPolynomial ℕ+ R :=
  AlgEquiv.refl

def synonymE {R : Type*} [CommSemiring R] (i : ℕ+) : Synonym R :=
  (synonymAlgEquiv R).symm (MvPolynomial.X i)

example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {f g : Synonym R →ₐ[R] A} (h : ∀ i, f (synonymE i) = g (synonymE i)) : f = g := by
  have h' : f.comp (synonymAlgEquiv R).symm.toAlgHom =
      g.comp (synonymAlgEquiv R).symm.toAlgHom := MvPolynomial.algHom_ext h
  ext p
  exact AlgHom.congr_fun h' (synonymAlgEquiv R p)

example {R : Type*} [CommRing R] (a b : Synonym R) :
    (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example {R : Type*} [CommRing R] (r : R) (a : Synonym R) :
    r • a = algebraMap R (Synonym R) r * a := Algebra.smul_def r a
end APIRepresentations
