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
