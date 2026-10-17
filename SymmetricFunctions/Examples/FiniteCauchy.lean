import SymmetricFunctions.Cauchy.Components
import Mathlib.Data.ZMod.Basic

/-! # Finite product alphabets and total degree conventions -/
noncomputable section
namespace SymmetricFunction.Examples
open SymmetricFunctions
open scoped TensorProduct

example : finiteCauchyProduct (Fin 0) (Fin 3) (ZMod 6) = 1 := by
  simp [finiteCauchyProduct]

-- Two powers in each alphabet contribute total degree four, with coefficient one.
example : MvPowerSeries.coeff
    ((Finsupp.single (0 : Fin 1) 2).sumElim (Finsupp.single (0 : Fin 1) 2))
      (finiteCauchyProduct (Fin 1) (Fin 1) (ZMod 6)) = 1 := by
  rw [coeff_finiteCauchyProduct]
  simp only [Fin.prod_univ_one, Finsupp.single_eq_same, coeff_hsymm,
    Finsupp.degree_single, ite_true]

-- Unequal alphabet degrees cannot contribute, even in a torsion coefficient ring.
example : MvPowerSeries.coeff
    ((Finsupp.single (0 : Fin 1) 1).sumElim (Finsupp.single (0 : Fin 1) 3))
      (finiteCauchyProduct (Fin 1) (Fin 1) (ZMod 6)) = 0 :=
  coeff_finiteCauchyProduct_eq_zero _ _ _ _ _ (by simp)

example : MvPowerSeries.homogeneousComponent 3
    (finiteCauchyProduct (Fin 2) (Fin 3) ℤ) = 0 :=
  homogeneousComponent_finiteCauchyProduct_odd 2 3 1

example (f g : SymmetricFunction (ZMod 6)) :
    completedTensorSpecialization (ZMod 6) 2 3
      (tensorCompletionMap (ZMod 6) (f ⊗ₜ[ZMod 6] g)) =
      (tensorAlphabetSpecialization (ZMod 6) (Fin 2) (Fin 3) (f ⊗ₜ[ZMod 6] g) :
        MvPowerSeries (Fin 2 ⊕ Fin 3) (ZMod 6)) :=
  completedTensorSpecialization_bounded _ _ _ _

end SymmetricFunction.Examples
