import SymmetricFunctions
noncomputable section
open SymmetricFunction
#check @stableEquiv
#print SymmetricFunction
#print SymmetricFunction.Compatible
#print SymmetricFunction.UniformlyBounded
#print PreLambdaRing
#print SpecialLambdaRing
#check @stableEquiv_symm_eq_lift
#check @comultiplication_e
#check @counit_e
#check @antipode_e
#check @comultiplication_h
#check @comultiplication_p
#check @comultiplication_mem_tensorDegree
#check @degreeZeroEquiv
#check @baseChange
#check @lambda_e_one
#check @lambdaHomEquiv
#check @lambdaEvaluation_preserves
#check @lambdaEval_natural
#check @SymmetricFunction.Examples.Torsion.projectionLambdaHom
#check @SymmetricFunction.Examples.Torsion.evaluation
#check @SymmetricFunction.Examples.Torsion.epsilon_ne_zero
#check @SymmetricFunction.Examples.Torsion.two_smul_epsilon
example (R : Type*) [CommRing R] : HopfAlgebra R (SymmetricFunction R) := inferInstance
example : SpecialLambdaRing SymmetricFunction.Examples.Torsion.Target := inferInstance
#print axioms stableEquiv
#print axioms comultiplication_e
#print axioms lambdaHomEquiv
#print axioms SymmetricFunction.Examples.Torsion.projectionLambdaHom
#print axioms SymmetricFunction.Examples.Torsion.evaluation_e_two
