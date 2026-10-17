import SymmetricFunctions

/-! Independent statement and proof-dependency review for the monomial milestone. -/
noncomputable section
open SymmetricFunction SymmetricFunctions
#print MvPolynomial.msymm
#print SymmetricFunctions.exponentParts
#check @MvPolynomial.coeff_msymm
#check @MvPolynomial.isHomogeneous_msymm
#check @MvPolynomial.killCompl_msymm
#check @zeroLast_msymm
#check @MvPolynomial.msymm_eq_zero_of_card_lt
#check @exists_mapDomain_eq_of_exponentParts_eq
#check @coeff_eq_of_exponentParts_eq
#check @MvPolynomial.eq_sum_msymm_of_representatives
#print SymmetricFunction.monomialFamily
#print SymmetricFunction.mPart
#check @rho_mPart
#check @coeff_rho_mPart
#check @isHomogeneous_mPart
#check @mPart_zero
#check @rho_mPart_eq_zero_of_card_lt
#check @monomialCoordinateEquiv
#check @mBasis
#check @mBasis_apply
#check @mBasis_repr_eq_coeff
#check @mBasisAll
#check @mBasisAll_apply
#check @mBasisAll_repr
example : Module.Basis (Nat.Partition 4) (ZMod 2)
    (homogeneousSubmodule (ZMod 2) 4) := mBasis (ZMod 2) 4
example : Module.Basis (Nat.Partition 4) PUnit (homogeneousSubmodule PUnit 4) := mBasis PUnit 4
#print axioms MvPolynomial.coeff_msymm
#print axioms rho_mPart
#print axioms mBasis
#print axioms mBasis_repr_eq_coeff
#print axioms mBasisAll
