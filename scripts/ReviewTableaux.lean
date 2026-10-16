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
