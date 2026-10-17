import SymmetricFunctions

/-! Statement and transitive-proof-dependency review, separate from compilation. -/
noncomputable section
open SymmetricFunction SymmetricFunctions
open scoped TensorProduct
#print inverseNewtonCoefficient
#print elementaryPowerCoordinates
#check @newtonCoefficient_mul_inverse
#check @powerSumSubstitution_elementaryPowerCoordinates
#check @inversePowerSumSubstitution_p
#print powerSumChangeOfGenerators
#print powerSumPolynomialEquiv
#check @powerSumPolynomialEquiv_X
#check @powerSumPolynomialEquiv_symm_p
#check @powerSumHomogeneous
#print pPart
#check @pBasis
#check @pBasis_apply
#check @pBasisAll
#check @pBasisAll_apply
#check @pBasisAll_repr
#print powerSumEval
#check @powerSumEval_p
#check @powerSumEval_algebraMap
#check @powerSumEvalEquiv
#check @algHom_ext_p
#check @powerSumEval_psum
#print negativeAlphabetEval
#print scaledAlphabetEval
#print powerSumAdams
#check @alphabetSpecialization_powerSumAdams
#check @tensorPowerSumPolynomialEquiv
#check @tensorAlphabetEval_unique
#check @tensorAlphabetEval_comp_comultiplication
#print MixedAlphabet
#check @mixedPowerSumPolynomialEquiv
#check @mixedAlphabetEval_unique
#print mixedAdams
#check @mixedAdams_X
#check @mixedAdams_p
#check @mixedAdams_comp
#print mixedPlethysticEval
#print geometricAlphabetEval
#check @geometricAlphabetEval_p_field
#check @geometricAlphabetEval_denominator
#check @geometricAlphabetEval_unique
#check @SymmetricFunction.Examples.ratFuncGeometricDenominators
-- Basis statements retain the zero ring; no Nontrivial assumption is hidden.
example : Module.Basis (Nat.Partition 4) PUnit (homogeneousSubmodule PUnit 4) := pBasis PUnit 4
-- Existing arbitrary-ring and torsion-target contracts remain available.
example : Module.Basis (Nat.Partition 4) (ZMod 2)
    (homogeneousSubmodule (ZMod 2) 4) := mBasis (ZMod 2) 4
#check @lambdaHomEquiv
#print axioms powerSumPolynomialEquiv
#print axioms pBasis
#print axioms pBasisAll
#print axioms powerSumEvalEquiv
#print axioms tensorAlphabetEval_comp_comultiplication
#print axioms mixedPowerSumPolynomialEquiv
#print axioms mixedAdams_comp
#print axioms geometricAlphabetEval_unique
#print axioms SymmetricFunction.Examples.ratFuncGeometricDenominators
