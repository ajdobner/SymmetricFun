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

#print elementaryInt
#print elementaryJacobiTrudiMatrix
#check @SymmetricFunctions.det_block_eq_det_mul_complement
#check @boundaryEquiv
#check @sign_boundary_relative_tail
#check @schur_eq_det_elementary_conjugate
#check @dual_jacobiTrudi
#check @omega_schur
#print axioms dual_jacobiTrudi
#print axioms omega_schur

#print hall
#print hallHomogeneous
#print hallHomogeneousPerfect
#print tensorHall
#print SymmetricFunctions.marginMatrices
#check @hall_hPart_mPart
#check @hall_hPart_eq_coeff
#check @hall_left_nondegenerate
#check @hall_right_nondegenerate
#check @hall_eq_zero_of_degrees_ne
#check @hallHomogeneousPerfect_apply
#check @hallHomogeneous_isPerfPair
#check @SymmetricFunctions.coeff_prod_hsymm
#check @SymmetricFunctions.card_marginMatrices_comm
#check @hall_symm
#check @tensorHall_tmul
#check @hall_mul
#check @hall_mul_right
#print axioms hall_symm
#print axioms hallHomogeneous_isPerfPair
#print axioms hall_mul
