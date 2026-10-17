import SymmetricFunctions.Schur.Triangular

/-!
# Integral Schur bases

The basis vectors are the already defined Jacobi–Trudi determinants. Their
complete-basis transition has determinant one. All constructions work over an
arbitrary commutative ring, including rings with torsion and the zero ring.
-/

namespace SymmetricFunction

noncomputable section
open scoped BigOperators DirectSum
open SymmetricFunctions

variable {R : Type*} [CommRing R] {d : ℕ}

private theorem schur_basis_conditions (R : Type*) [CommRing R] (d : ℕ) :
    LinearIndependent R (fun ξ : Nat.Partition d =>
      (⟨schur ξ, isHomogeneous_schur ξ⟩ : homogeneousSubmodule R d)) ∧
    Submodule.span R (Set.range (fun ξ : Nat.Partition d =>
      (⟨schur ξ, isHomogeneous_schur ξ⟩ : homogeneousSubmodule R d))) = ⊤ := by
  apply (Module.Basis.is_basis_iff_det (hBasis R d)).mpr
  have hm : (hBasis R d).toMatrix (fun ξ : Nat.Partition d =>
      (⟨schur ξ, isHomogeneous_schur ξ⟩ : homogeneousSubmodule R d)) =
      schurCompleteTransition R d := by
    ext μ ξ
    exact (schurCompleteTransition_eq_repr μ ξ).symm
  rw [Module.Basis.det_apply, hm, det_schurCompleteTransition]
  exact isUnit_one

/-- The actual determinant Schur basis of weighted degree d. -/
def schurBasis (R : Type*) [CommRing R] (d : ℕ) :
    Module.Basis (Nat.Partition d) R (homogeneousSubmodule R d) :=
  Module.Basis.mk (schur_basis_conditions R d).1 (schur_basis_conditions R d).2.ge

@[simp] theorem schurBasis_apply (ξ : Nat.Partition d) :
    (schurBasis R d ξ : SymmetricFunction R) = schur ξ := by
  rw [schurBasis, Module.Basis.mk_apply]

/-- The graded Schur basis of the bounded symmetric-function ring. -/
def schurBasisAll (R : Type*) [CommRing R] :
    Module.Basis (Σ d, Nat.Partition d) R (SymmetricFunction R) :=
  (DFinsupp.basis (schurBasis R)).map (decompose R).symm.toLinearEquiv

@[simp] theorem schurBasisAll_apply (ξ : Σ d, Nat.Partition d) :
    schurBasisAll R ξ = schur ξ.2 := by
  rw [schurBasisAll, Module.Basis.map_apply]
  have hb : DFinsupp.basis (schurBasis R) ξ =
      DirectSum.lof R ℕ (fun d => homogeneousSubmodule R d) ξ.1 (schurBasis R ξ.1 ξ.2) := by
    simp [DFinsupp.basis, Module.Basis.coe_ofRepr]
    rfl
  rw [hb]
  exact (DirectSum.decomposeLinearEquiv_symm_lof (homogeneousSubmodule R) _ _).trans
    (schurBasis_apply ξ.2)

/-- The full coordinates are the homogeneous coordinates of the matching layer. -/
theorem schurBasisAll_repr (f : SymmetricFunction R) (ξ : Σ d, Nat.Partition d) :
    (schurBasisAll R).repr f ξ = (schurBasis R ξ.1).repr (decompose R f ξ.1) ξ.2 := rfl

/-- Every bounded symmetric function has a finite Schur expansion. -/
theorem sum_schurBasisAll_repr (f : SymmetricFunction R) :
    ∑ ξ ∈ ((schurBasisAll R).repr f).support,
      (schurBasisAll R).repr f ξ • schur ξ.2 = f := by
  classical
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum, schurBasisAll_apply] using
    (schurBasisAll R).linearCombination_repr f

/-- Equality is determined by all Schur coefficients. -/
theorem ext_schur_coefficients {f g : SymmetricFunction R}
    (hfg : ∀ ξ, (schurBasisAll R).repr f ξ = (schurBasisAll R).repr g ξ) : f = g :=
  (schurBasisAll R).repr.injective (Finsupp.ext hfg)

/-- The degree-d expansion uses exactly the partitions of d. -/
theorem sum_schurBasis_repr (f : homogeneousSubmodule R d) :
    ∑ ξ : Nat.Partition d, (schurBasis R d).repr f ξ • schur ξ = (f : SymmetricFunction R) := by
  classical
  simpa only [Submodule.coe_sum, Submodule.coe_smul, schurBasis_apply] using
    congrArg (fun x : homogeneousSubmodule R d => (x : SymmetricFunction R))
      ((schurBasis R d).sum_repr f)

end
end SymmetricFunction
