import SymmetricFunctions.Basis.Monomial
import SymmetricFunctions.Notation
import Mathlib.Data.ZMod.Basic

/-! # Empty, repeated-part and small-alphabet monomial conventions -/

noncomputable section

open SymmetricFunction SymmetricFunctions MvPolynomial
open scoped SymmetricFunctionNotation

namespace SymmetricFunctions.Examples.Monomial

/-- Two equal parts: the finite orbit has coefficient one, without a factorial. -/
def repeatedTwo : Nat.Partition 4 := ⟨{2, 2}, by simp, by decide⟩

def twoVariableExponent : Fin 2 →₀ ℕ := Finsupp.single 0 2 + Finsupp.single 1 2

private theorem exponentParts_twoVariableExponent :
    exponentParts twoVariableExponent = repeatedTwo.parts := by
  have hs : twoVariableExponent.support = {0, 1} := by
    ext i
    fin_cases i <;> simp [twoVariableExponent, Finsupp.mem_support_iff]
  rw [exponentParts, hs]
  simp [twoVariableExponent, repeatedTwo]

attribute [local irreducible] SymmetricFunction

example {R : Type*} [CommRing R] : mPart (R := R) (Nat.Partition.indiscrete 0) = 1 := by simp

example {R : Type*} [CommRing R] :
    (rho R 2 (mPart repeatedTwo)).val.coeff twoVariableExponent = 1 := by
  rw [coeff_rho_mPart, exponentParts_twoVariableExponent, ite_eq_left rfl]

example : (rho (ZMod 2) 2 (mPart repeatedTwo)).val.coeff twoVariableExponent = 1 := by
  rw [coeff_rho_mPart, exponentParts_twoVariableExponent, ite_eq_left rfl]

example {R : Type*} [CommRing R] : rho R 1 (mPart repeatedTwo) = 0 :=
  rho_mPart_eq_zero_of_card_lt 1 repeatedTwo (by decide)

example {R : Type*} [CommRing R] :
    (rho R 0 (mPart (Nat.Partition.indiscrete 0))).val.coeff 0 = 1 := by simp

example {R : Type*} [CommRing R] : mBasisAll R ⟨0, Nat.Partition.indiscrete 0⟩ = 1 := by simp

example : Module.Basis (Nat.Partition 4) (ZMod 2)
    (homogeneousSubmodule (ZMod 2) 4) := mBasis (ZMod 2) 4

example : Module.Basis (Nat.Partition 4) PUnit (homogeneousSubmodule PUnit 4) := mBasis PUnit 4

-- A different exponent representative has the same coordinate; no alphabet-size premise is needed.
example {R : Type*} [CommRing R] (f : homogeneousSubmodule R 4) :
    (mBasis R 4).repr f repeatedTwo = (rho R 2 f).val.coeff twoVariableExponent :=
  mBasis_repr_eq_coeff f repeatedTwo 2 twoVariableExponent exponentParts_twoVariableExponent

end SymmetricFunctions.Examples.Monomial
