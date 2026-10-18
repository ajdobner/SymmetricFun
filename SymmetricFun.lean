module

public import SymmetricFun.Partition.Dominance
public import SymmetricFun.SymmetricFunction.Basic
public import SymmetricFun.SymmetricFunction.Grading
public import SymmetricFun.SymmetricFunction.Basis.Defs
public import SymmetricFun.SymmetricFunction.Basis.Monomial
public import SymmetricFun.SymmetricFunction.Basis.Elementary
public import SymmetricFun.SymmetricFunction.Basis.Complete
public import SymmetricFun.SymmetricFunction.Basis.Transition.ElementaryComplete
public import SymmetricFun.SymmetricFunction.Omega

/-!
# Symmetric functions

This umbrella module imports the concrete power-series construction, its grading, and the
monomial, elementary, and complete homogeneous symmetric functions.
It also includes the monomial, elementary, and complete homogeneous bases and the
binary-matrix count for elementary-to-monomial coefficients, together with the graded
polynomial presentations in the elementary and complete homogeneous generators.
The elementary–complete relation gives their alternating convolution in every degree.
The graded algebra involution `omega` exchanges the elementary and complete homogeneous
functions and their partition products.
-/
