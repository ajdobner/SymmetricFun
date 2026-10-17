import SymmetricFunctions

/-! Definitions and hypotheses reviewed independently of the proofs. -/
open SymmetricFunctions.Partition
#print FiniteTableau
#print FiniteTableau.filling
#print FiniteTableau.content
#print FiniteTableau.weight
#print FiniteTableau.generatingPolynomial
#print FiniteTableau.contentCount
#check @FiniteTableau.filling_injective
#check @FiniteTableau.content_apply
#check @FiniteTableau.degree_content
#check @FiniteTableau.weight_eq_prod
#check @FiniteTableau.coeff_generatingPolynomial
#check @FiniteTableau.map_generatingPolynomial
#check @FiniteTableau.nonempty_iff
#check @FiniteTableau.generatingPolynomial_zero
#check @FiniteTableau.generatingPolynomial_zero_alphabet
#check @FiniteTableau.generatingPolynomial_eq_zero_of_length_gt
#print axioms FiniteTableau.degree_content
#print axioms FiniteTableau.coeff_generatingPolynomial
#print axioms FiniteTableau.nonempty_iff
#print axioms FiniteTableau.generatingPolynomial_zero

#print HorizontalStrip
#print SkewCell
#print SkewTableau
#print SkewTableau.content
#print SkewTableau.generatingPolynomial
#check @HorizontalStrip.eq_row_of_cells
#check @horizontalStrip_of_column_injective
#check @SkewTableau.degree_content
#check @SkewTableau.coeff_generatingPolynomial
#check @SkewTableau.straightEquiv
#check @SkewTableau.content_ofStraight
#check @SkewTableau.generatingPolynomial_empty
#check @SkewTableau.generatingPolynomial_self
#check @SkewTableau.generatingPolynomial_eq_zero_of_not_contained
#check @SkewTableau.nonempty_one_iff
#check @SkewTableau.generatingPolynomial_one
#print axioms SkewTableau.degree_content
#print axioms SkewTableau.straightEquiv
#print axioms SkewTableau.generatingPolynomial_empty
#print axioms SkewTableau.generatingPolynomial_one

open SymmetricFunction
#print oneLetterEvaluation
#print skewThresholdMatrix
#check @SymmetricFunctions.homogeneous_finOne
#check @oneLetterEvaluation_skewSchur
#check @alphabetSpecialization_one_skewSchur
#check @comultiplication_skewing
#check @comultiplication_skewSchur
#check @alphabetSpecialization_succ_skewSchur
#check @alphabetSpecialization_one_skewSchur_eq_tableaux
#print axioms alphabetSpecialization_one_skewSchur
#print axioms alphabetSpecialization_succ_skewSchur
#print axioms alphabetSpecialization_one_skewSchur_eq_tableaux
