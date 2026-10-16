import SymmetricFunctions

/-! SCHUR statement review: inspect definitions independently of successful proofs.
This file grows at each accepted checkpoint; it does not assert unfinished contracts. -/
open SymmetricFunctions.Partition
#print rowLength
#print length
#print Contained
#print FiniteTableau
#check @rowLength_eq_getElem_sort
#check @rowLength_eq_zero
#check @sum_rowLength_padded
#check @contained_iff_rowLength
#check @ofPartition_conjugate
#check @rowLength_indiscrete_conjugate
#print axioms sum_rowLength_padded
#print axioms rowLength_indiscrete_conjugate

open SymmetricFunction
#print completeInt
#print jacobiTrudiMatrix
#print schur
#print finiteCompleteInt
#print SymmetricFunctions.upperToeplitz
#check @det_jacobiTrudiMatrix
#check @isHomogeneous_schur
#check @map_schur
#check @rho_schur
#check @schur_zero
#check @schur_indiscrete
#check @schur_indiscrete_conjugate
#check @SymmetricFunctions.upperToeplitzHom
#print axioms isHomogeneous_schur
#print axioms schur_indiscrete_conjugate

#print squareWeight
#print schurCompleteTransition
#check @sum_sq_jacobiTrudiIndex_gt
#check @schurCompleteTransition_eq_delta_of_le
#check @det_schurCompleteTransition
#check @schurBasis
#check @schurBasis_apply
#check @schurBasisAll
#check @schurBasisAll_apply
#check @sum_schurBasisAll_repr
#check @ext_schur_coefficients
#print axioms schurBasis
#print axioms schurBasisAll
