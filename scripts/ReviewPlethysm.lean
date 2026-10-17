import SymmetricFunctions

/-! Independent elaborated-statement review for PLETH. -/
noncomputable section
open SymmetricFunction
open scoped TensorProduct
#print SymmetricFunction.plethysm
#check @plethysm_assoc
#check @e_one_plethysm
#check @plethysm_e_one
#print SymmetricFunction.adams
#check @rhoPolynomial_adams
#check @plethysm_p
#check @adams_p
#check @adams_comp
#check @lambdaEval_p_polynomial
#check @plethysm_p_neg
#check @tensorPolynomialEquiv
#check @eq_of_tensorAlphabetSpecialization_eq
#print SymmetricFunction.TensorAlphabetFamily
#check @lambda_mem_range_tensorAlphabetEmbedding
#check @tensorAlphabetSpecialization_lambda
#check @tensorLeftLambdaHom
#check @tensorRightLambdaHom
#check @comultiplication_eq_lambdaEval
#check @comultiplicationLambdaHom
#check @comultiplication_plethysm
#check @LambdaRing.lambdaStableSubring
#check @LambdaRing.piSpecialLambdaRing
#check @SpecialLambdaRing.ofInjective
example : SpecialLambdaRing (SymmetricFunction ℤ ⊗[ℤ] SymmetricFunction ℤ) := inferInstance
example (R : Type*) [CommRing R] : HopfAlgebra R (SymmetricFunction R) := inferInstance
example : SpecialLambdaRing SymmetricFunction.Examples.Torsion.Target := inferInstance
#print axioms plethysm_p
#print axioms lambdaEval_p_polynomial
#print axioms tensorSpecialLambdaRing
#print axioms comultiplicationLambdaHom
#print axioms comultiplication_plethysm
