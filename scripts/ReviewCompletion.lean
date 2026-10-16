import SymmetricFunctions

/-! Parent contract review: read these definitions and statements independently of proofs. -/
open SymmetricFunctions SymmetricFunctions.Series SymmetricFunction
#print HasBoundedTotalDegree
#print GradedCompletion
#print DegreeCompletion
#print CompletedTensor
#print completeSeries
#print signedElementarySeries
#print MvPowerSeries.HasSubst
#check @boundedSeriesEquiv
#check @finiteRestriction_toSeries_e
#check @finiteRestriction_toSeries_h
#check @coeff_toSeries_mPart
#check @completionEmbedding_injective
#check @DegreeCompletion.component_mul
#check @DegreeCompletion.truncate_mul
#check @completionSeriesEquiv
#check @completeSeries_mul_signedElementarySeries
#check @completedCoproduct_embedding
#check @completedCoproduct_completeSeries
#check @completedSubstitution_coefficient_finite
#check @truncTotal_completedSubstitution
#check @completedFiniteEval_embedding_eq_eval
#check @completedFiniteEval_complete_one_mul
#print axioms boundedSeriesEquiv
#print axioms completionSeriesEquiv
#print axioms completedCoproduct_completeSeries
#print axioms completedFiniteEval_complete_one_mul
