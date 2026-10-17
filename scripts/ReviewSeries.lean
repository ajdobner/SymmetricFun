import SymmetricFunctions

/-! Separate inspection of mathematical statements, not just compilation. -/
open SymmetricFunctions SymmetricFunctions.Series SymmetricFunction
#print SymmetricFunctions.Series.IsSymmetric
#print HasBoundedTotalDegree
#print boundedSymmetricSubalgebra
#print exponentPartition
#print monomialSeries
#check @IsSymmetric.coeff_eq
#check @isSymmetric_of_coeff_eq
#check @eq_of_finiteRestriction_eq
#check @toSeries
#check @coeff_toSeries
#check @finiteRestriction_toSeries
#check @boundedSeriesMap_surjective
#check @boundedSeriesEquiv
#check @isHomogeneous_toSeries
#check @toSeries_homogeneousComponent
#check @finiteRestriction_toSeries_e
#check @finiteRestriction_toSeries_h
#check @coeff_toSeries_mPart
#print axioms boundedSeriesEquiv
#print axioms toSeries_homogeneousComponent
#print axioms finiteRestriction_toSeries_h
#print axioms coeff_toSeries_mPart
