import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Environment compatibility checks

These small examples exercise the dependencies of the planned development.
They do not define the public symmetric-function type or claim any roadmap theorem.
-/

set_option linter.style.header false

namespace SymmetricFunctions.Environment

noncomputable section

example (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial.symmetricSubalgebra (Fin n) R :=
  MvPolynomial.esymmAlgEquiv (Fin n) R (by simp)

example (R : Type*) [CommRing R] :
    GradedAlgebra
      (MvPolynomial.weightedHomogeneousSubmodule R (fun i : ℕ+ => (i : ℕ))) :=
  MvPolynomial.weightedGradedAlgebra R (fun i : ℕ+ => (i : ℕ))

/-- Named smoke declaration for the transitive axiom check. -/
theorem elementary_zero (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial.esymm (Fin n) R 0 = 1 := by
  simp

example (R A : Type*) [CommRing R] [CommRing A] [HopfAlgebra R A] :
    A →ₗ[R] A := HopfAlgebra.antipode R (A := A)

end

end SymmetricFunctions.Environment
