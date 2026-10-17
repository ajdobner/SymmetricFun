import SymmetricFunctions.Partition.Orbits
import SymmetricFunctions.Basis.Elementary

/-! # Monomial symmetric functions from the bounded stable realization

These functions lift Mathlib's finite exponent-orbit sums over arbitrary
commutative coefficient rings. Their finite coefficients are shape indicators.
-/

noncomputable section

namespace SymmetricFunction

open SymmetricFunctions MvPolynomial
variable (R : Type*) [CommRing R]

/-- The bounded compatible family of finite monomial symmetric orbit sums. -/
def monomialFamily {d : ℕ} (μ : Nat.Partition d) : BoundedStable R :=
  ⟨fun N => ⟨msymm (Fin N) R μ, msymm_isSymmetric _ _ _⟩,
    (by
      intro N
      apply Subtype.ext
      rw [coe_transition]
      exact zeroLast_msymm R N μ),
    ⟨d, fun _ => (isHomogeneous_msymm μ).totalDegree_le⟩⟩

variable {R}

/-- The monomial symmetric function indexed by a Mathlib partition. -/
def mPart {d : ℕ} (μ : Nat.Partition d) : SymmetricFunction R :=
  (stableEquiv R).symm (monomialFamily R μ)

/-- Recovery in every finite alphabet, including below the stable range. -/
@[simp] theorem rho_mPart {d : ℕ} (N : ℕ) (μ : Nat.Partition d) :
    (rho R N (mPart (R := R) μ)).val = msymm (Fin N) R μ := by
  rw [mPart, rho_stableEquiv_symm]
  rfl

/-- Coefficient one on the exponent orbit, coefficient zero everywhere else. -/
theorem coeff_rho_mPart {d : ℕ} (N : ℕ) (μ : Nat.Partition d) (a : Fin N →₀ ℕ) :
    (rho R N (mPart (R := R) μ)).val.coeff a =
      if exponentParts a = μ.parts then 1 else 0 := by
  rw [rho_mPart, coeff_msymm]

theorem isHomogeneous_mPart {d : ℕ} (μ : Nat.Partition d) :
    SymmetricFunction.IsHomogeneous (mPart (R := R) μ) d := by
  rw [mPart, stableEquiv_symm_eq_lift R (monomialFamily R μ)
    (d := d) (N := d) (fun _ => (isHomogeneous_msymm μ).totalDegree_le) le_rfl]
  exact isHomogeneous_liftSymmetric R d d _ (isHomogeneous_msymm μ)

@[simp] theorem mPart_zero (μ : Nat.Partition 0) : mPart (R := R) μ = 1 := by
  apply (stableEquiv R).injective
  apply Subtype.ext
  funext N
  apply Subtype.ext
  simp only [stableEquiv_apply, rho_mPart, map_one, OneMemClass.coe_one]
  have hμ : μ = Nat.Partition.indiscrete 0 := Subsingleton.elim _ _
  rw [hμ, msymm_zero]
  rfl

/-- A partition with too many parts vanishes in a small alphabet. -/
theorem rho_mPart_eq_zero_of_card_lt {d : ℕ} (N : ℕ) (μ : Nat.Partition d)
    (hμ : N < μ.parts.card) : rho R N (mPart (R := R) μ) = 0 := by
  apply Subtype.ext
  rw [rho_mPart]
  exact msymm_eq_zero_of_card_lt μ (by simpa using hμ)


/-- Stable coefficients at representatives are Kronecker delta on partition vectors. -/
@[simp] theorem coeff_rho_mPart_representative {d : ℕ} (μ ν : Nat.Partition d) :
    (rho R d (mPart (R := R) μ)).val.coeff (Partition.representative ν) =
      if μ = ν then 1 else 0 := by
  rw [coeff_rho_mPart, Partition.exponentParts_representative]
  have he : ν.parts = μ.parts ↔ μ = ν :=
    ⟨fun h => (Nat.Partition.ext h).symm, fun h => by rw [h]⟩
  simp only [he]

/-- Coordinates obtained from actual finite-alphabet coefficients. -/
def monomialCoordinates (R : Type*) [CommRing R] (d : ℕ) :
    homogeneousSubmodule R d →ₗ[R] (Nat.Partition d → R) where
  toFun f μ := (rho R d f).val.coeff (Partition.representative μ)
  map_add' f g := by
    funext μ
    simp
  map_smul' r f := by
    funext μ
    simp

/-- Reconstruct a homogeneous function from its partition coefficients. -/
def monomialSynthesis (R : Type*) [CommRing R] (d : ℕ) (c : Nat.Partition d → R) :
    homogeneousSubmodule R d :=
  ⟨∑ μ, c μ • mPart μ, (homogeneousSubmodule R d).sum_mem fun μ _ =>
    (homogeneousSubmodule R d).smul_mem (c μ) (isHomogeneous_mPart μ)⟩

theorem monomialSynthesis_coordinates {d : ℕ} (f : homogeneousSubmodule R d) :
    monomialSynthesis R d (monomialCoordinates R d f) = f := by
  apply Subtype.ext
  apply (rho_eq_iff_of_degreeLE R (N := d) le_rfl
    (homogeneous_le_degreeLE le_rfl (monomialSynthesis R d _).property)
    (homogeneous_le_degreeLE le_rfl f.property)).mp
  apply Subtype.ext
  simpa [monomialSynthesis, monomialCoordinates] using
    (eq_sum_msymm_of_representatives (rho R d f).val (rho R d f).property
      (isHomogeneous_rho R d d f f.property) Partition.representative
      Partition.exponentParts_representative).symm

theorem monomialCoordinates_synthesis {d : ℕ} (c : Nat.Partition d → R) :
    monomialCoordinates R d (monomialSynthesis R d c) = c := by
  classical
  funext ν
  simp [monomialCoordinates, monomialSynthesis, coeff_msymm,
    Partition.exponentParts_representative, ← Nat.Partition.ext_iff]

/-- Coordinates and reconstruction are inverse, over every commutative ring. -/
def monomialCoordinateEquiv (R : Type*) [CommRing R] (d : ℕ) :
    homogeneousSubmodule R d ≃ₗ[R] (Nat.Partition d → R) :=
  { monomialCoordinates R d with
    invFun := monomialSynthesis R d
    left_inv := monomialSynthesis_coordinates
    right_inv := monomialCoordinates_synthesis }

/-- The actual monomial partition basis of the degree-d component. -/
def mBasis (R : Type*) [CommRing R] (d : ℕ) :
    Module.Basis (Nat.Partition d) R (homogeneousSubmodule R d) :=
  Module.Basis.ofEquivFun (monomialCoordinateEquiv R d)

@[simp] theorem mBasis_apply {d : ℕ} (μ : Nat.Partition d) :
    (mBasis R d μ : SymmetricFunction R) = mPart μ := by
  classical
  simp [mBasis, Module.Basis.coe_ofEquivFun, monomialCoordinateEquiv, monomialSynthesis]

/-- Basis coordinates equal coefficients at any chosen orbit representative. -/
theorem mBasis_repr {d : ℕ} (f : homogeneousSubmodule R d) (μ : Nat.Partition d) :
    (mBasis R d).repr f μ = (rho R d f).val.coeff (Partition.representative μ) := rfl


/-- The coefficient interpretation does not depend on the chosen representative or alphabet size. -/
theorem mBasis_repr_eq_coeff {d : ℕ} (f : homogeneousSubmodule R d)
    (μ : Nat.Partition d) (N : ℕ) (a : Fin N →₀ ℕ) (ha : exponentParts a = μ.parts) :
    (mBasis R d).repr f μ = (rho R N f).val.coeff a := by
  classical
  have he := congrArg (fun g : homogeneousSubmodule R d => (rho R N g).val.coeff a)
    ((mBasis R d).sum_repr f)
  have hs (ν : Nat.Partition d) : exponentParts a = ν.parts ↔ μ = ν :=
    ⟨fun h => Nat.Partition.ext (ha.symm.trans h), fun h => ha.trans (congrArg _ h)⟩
  simp only [Submodule.coe_smul, map_sum, map_smul,
    AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, mBasis_apply, rho_mPart,
    coeff_sum, coeff_smul, coeff_msymm, hs, smul_eq_mul] at he
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true] using he

open scoped DirectSum in
/-- The monomial basis of all bounded symmetric functions, indexed by all partitions. -/
def mBasisAll (R : Type*) [CommRing R] :
    Module.Basis (Σ d, Nat.Partition d) R (SymmetricFunction R) :=
  (DFinsupp.basis (mBasis R)).map (decompose R).symm.toLinearEquiv

open scoped DirectSum in
@[simp] theorem mBasisAll_apply (μ : Σ d, Nat.Partition d) :
    mBasisAll R μ = mPart μ.2 := by
  rw [mBasisAll, Module.Basis.map_apply]
  have h : DFinsupp.basis (mBasis R) μ =
      DirectSum.lof R ℕ (fun d => homogeneousSubmodule R d) μ.1 (mBasis R μ.1 μ.2) := by
    simp [DFinsupp.basis, Module.Basis.coe_ofRepr]
    rfl
  rw [h]
  exact (DirectSum.decomposeLinearEquiv_symm_lof (homogeneousSubmodule R) _ _).trans
    (mBasis_apply μ.2)

/-- Full-basis coordinates extract finite coefficients of the indicated homogeneous component. -/
theorem mBasisAll_repr (f : SymmetricFunction R) (μ : Σ d, Nat.Partition d) :
    (mBasisAll R).repr f μ =
      (rho R μ.1 (homogeneousComponent μ.1 f)).val.coeff (Partition.representative μ.2) := by
  change (mBasis R μ.1).repr (decompose R f μ.1) μ.2 = _
  exact mBasis_repr _ _

end SymmetricFunction
