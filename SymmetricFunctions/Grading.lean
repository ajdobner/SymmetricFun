import SymmetricFunctions.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Weighted grading and the degree filtration

The positive elementary generator `e i` has degree `i`. The filtration consists
of finite sums of homogeneous pieces; its terms are submodules, not subalgebras.
All constructions allow the zero coefficient ring.
-/

namespace SymmetricFunction

noncomputable section

open scoped DirectSum BigOperators

variable {R : Type*} [CommSemiring R]

/-- Homogeneity in symmetric-function degree. -/
def IsHomogeneous (f : SymmetricFunction R) (d : ℕ) : Prop :=
  MvPolynomial.IsWeightedHomogeneous (fun i : ℕ+ => (i : ℕ)) (polynomialEquiv R f) d

/-- The degree-`d` homogeneous component as a submodule. -/
def homogeneousSubmodule (R : Type*) [CommSemiring R] (d : ℕ) :
    Submodule R (SymmetricFunction R) :=
  (MvPolynomial.weightedHomogeneousSubmodule R (fun i : ℕ+ => (i : ℕ)) d).comap
    (polynomialEquiv R).toLinearMap

@[simp] theorem mem_homogeneousSubmodule (f : SymmetricFunction R) (d : ℕ) :
    f ∈ homogeneousSubmodule R d ↔ IsHomogeneous f d := Iff.rfl

-- This is the instance-transfer boundary of the polynomial presentation.
instance : GradedAlgebra (homogeneousSubmodule R) :=
  MvPolynomial.weightedGradedAlgebra R (fun i : ℕ+ => (i : ℕ))

/-- The algebra equivalence with the direct sum of homogeneous pieces. -/
def decompose (R : Type*) [CommSemiring R] :
    SymmetricFunction R ≃ₐ[R] ⨁ d : ℕ, homogeneousSubmodule R d :=
  DirectSum.decomposeAlgEquiv (homogeneousSubmodule R)

/-- Projection onto the degree-`d` homogeneous component. -/
def homogeneousComponent (d : ℕ) : SymmetricFunction R →ₗ[R] SymmetricFunction R :=
  GradedAlgebra.proj (homogeneousSubmodule R) d

@[simp] theorem homogeneousComponent_eq_decompose (d : ℕ) (f : SymmetricFunction R) :
    homogeneousComponent d f = (decompose R f d : SymmetricFunction R) := rfl

theorem polynomialEquiv_homogeneousComponent (d : ℕ) (f : SymmetricFunction R) :
    polynomialEquiv R (homogeneousComponent d f) =
      MvPolynomial.weightedHomogeneousComponent (fun i : ℕ+ => (i : ℕ)) d
        (polynomialEquiv R f) :=
  MvPolynomial.weightedDecomposition.decompose'_apply R _ _ _

theorem homogeneousComponent_mem (d : ℕ) (f : SymmetricFunction R) :
    IsHomogeneous (homogeneousComponent d f) d := (decompose R f d).property

theorem homogeneousComponent_of_mem {f : SymmetricFunction R} {d : ℕ}
    (hf : IsHomogeneous f d) : homogeneousComponent d f = f :=
  DirectSum.decompose_of_mem_same (homogeneousSubmodule R) hf

theorem homogeneousComponent_of_mem_ne {f : SymmetricFunction R} {d k : ℕ}
    (hf : IsHomogeneous f d) (h : d ≠ k) : homogeneousComponent k f = 0 :=
  DirectSum.decompose_of_mem_ne (homogeneousSubmodule R) hf h

open scoped Classical in
/-- Every symmetric function has a finite homogeneous expansion. -/
theorem sum_homogeneousComponent (f : SymmetricFunction R) :
    ∑ d ∈ (decompose R f).support, homogeneousComponent d f = f :=
  DirectSum.sum_support_decompose (homogeneousSubmodule R) f

@[simp] theorem isHomogeneous_zero (d : ℕ) : IsHomogeneous (0 : SymmetricFunction R) d :=
  (homogeneousSubmodule R d).zero_mem

@[simp] theorem isHomogeneous_one : IsHomogeneous (1 : SymmetricFunction R) 0 := by
  change (1 : SymmetricFunction R) ∈ homogeneousSubmodule R 0
  exact SetLike.GradedOne.one_mem

theorem isHomogeneous_algebraMap (r : R) :
    IsHomogeneous (algebraMap R (SymmetricFunction R) r) 0 := by
  change MvPolynomial.IsWeightedHomogeneous _ (polynomialEquiv R (algebraMap _ _ r)) 0
  rw [AlgEquiv.commutes]
  exact MvPolynomial.isWeightedHomogeneous_C _ r

@[simp] theorem isHomogeneous_e (n : ℕ) : IsHomogeneous (e (R := R) n) n := by
  cases n with
  | zero => simp
  | succ n =>
    unfold IsHomogeneous
    rw [polynomialEquiv_e_succ]
    exact MvPolynomial.isWeightedHomogeneous_X R (fun i : ℕ+ => (i : ℕ))
      ⟨n + 1, Nat.succ_pos n⟩

namespace IsHomogeneous

variable {f g : SymmetricFunction R} {m n : ℕ}

theorem add (hf : IsHomogeneous f n) (hg : IsHomogeneous g n) :
    IsHomogeneous (f + g) n := (homogeneousSubmodule R n).add_mem hf hg

theorem smul (hf : IsHomogeneous f n) (r : R) : IsHomogeneous (r • f) n :=
  (homogeneousSubmodule R n).smul_mem r hf

theorem mul (hf : IsHomogeneous f m) (hg : IsHomogeneous g n) :
    IsHomogeneous (f * g) (m + n) := by
  change f * g ∈ homogeneousSubmodule R (m + n)
  exact SetLike.GradedMul.mul_mem
    (show f ∈ homogeneousSubmodule R m from hf) (show g ∈ homogeneousSubmodule R n from hg)

theorem pow (hf : IsHomogeneous f m) (k : ℕ) : IsHomogeneous (f ^ k) (k * m) := by
  unfold IsHomogeneous at *
  simpa using hf.pow k

end IsHomogeneous

/-- Degree zero consists precisely of constants, also over the zero ring. -/
theorem isHomogeneous_zero_iff (f : SymmetricFunction R) :
    IsHomogeneous f 0 ↔ ∃ r, f = algebraMap R (SymmetricFunction R) r := by
  constructor
  · intro hf
    refine ⟨(polynomialEquiv R f).coeff 0, ?_⟩
    apply (polynomialEquiv R).injective
    conv_lhs => rw [← homogeneousComponent_of_mem hf, polynomialEquiv_homogeneousComponent]
    rw [MvPolynomial.weightedHomogeneousComponent_zero _ (fun i => i.pos.ne')]
    rw [AlgEquiv.commutes]
    rfl
  · rintro ⟨r, rfl⟩
    exact isHomogeneous_algebraMap r

/-- Functions of degree at most `d`, as finite sums of homogeneous pieces. -/
def degreeLE (R : Type*) [CommSemiring R] (d : ℕ) : Submodule R (SymmetricFunction R) :=
  ⨆ k ≤ d, homogeneousSubmodule R k

theorem homogeneous_le_degreeLE {k d : ℕ} (h : k ≤ d) :
    homogeneousSubmodule R k ≤ degreeLE R d :=
  le_iSup_of_le k (le_iSup_of_le h le_rfl)

theorem degreeLE_mono {m n : ℕ} (h : m ≤ n) : degreeLE R m ≤ degreeLE R n := by
  refine iSup_le fun k => iSup_le fun hk => ?_
  exact homogeneous_le_degreeLE (hk.trans h)

@[simp] theorem degreeLE_zero : degreeLE R 0 = homogeneousSubmodule R 0 := by
  simp [degreeLE]

theorem e_mem_degreeLE (n : ℕ) : e (R := R) n ∈ degreeLE R n :=
  homogeneous_le_degreeLE le_rfl (isHomogeneous_e n)

theorem algebraMap_mem_degreeLE (r : R) (d : ℕ) :
    algebraMap R (SymmetricFunction R) r ∈ degreeLE R d :=
  homogeneous_le_degreeLE (Nat.zero_le d) (isHomogeneous_algebraMap r)

/-- Multiplication adds degree bounds. -/
theorem degreeLE_mul (m n : ℕ) : degreeLE R m * degreeLE R n ≤ degreeLE R (m + n) := by
  unfold degreeLE
  simp only [Submodule.iSup_mul, Submodule.mul_iSup]
  refine iSup_le fun i => iSup_le fun hi => iSup_le fun j => iSup_le fun hj => ?_
  refine le_trans ?_ (le_iSup_of_le (j + i) (le_iSup_of_le (Nat.add_le_add hj hi) le_rfl))
  exact Submodule.mul_le.mpr fun _ hf _ hg => IsHomogeneous.mul hf hg

theorem mul_mem_degreeLE {f g : SymmetricFunction R} {m n : ℕ}
    (hf : f ∈ degreeLE R m) (hg : g ∈ degreeLE R n) : f * g ∈ degreeLE R (m + n) :=
  degreeLE_mul m n (Submodule.mul_mem_mul hf hg)

/-- The filtration bound is equivalent to vanishing of all higher components. -/
theorem mem_degreeLE_iff {f : SymmetricFunction R} {d : ℕ} :
    f ∈ degreeLE R d ↔ ∀ k, d < k → homogeneousComponent k f = 0 := by
  constructor
  · intro hf k hk
    have hle : degreeLE R d ≤ LinearMap.ker (homogeneousComponent k) := by
      refine iSup_le fun i => iSup_le fun hi => ?_
      intro g hg
      exact homogeneousComponent_of_mem_ne hg (Nat.ne_of_lt (hi.trans_lt hk))
    exact hle hf
  · intro hf
    classical
    rw [← sum_homogeneousComponent f]
    apply (degreeLE R d).sum_mem
    intro k _
    by_cases hk : k ≤ d
    · exact homogeneous_le_degreeLE hk (homogeneousComponent_mem k f)
    · rw [hf k (Nat.lt_of_not_ge hk)]
      exact (degreeLE R d).zero_mem

/-- Each element has a finite degree bound. No completion is present. -/
theorem exists_mem_degreeLE (f : SymmetricFunction R) : ∃ d, f ∈ degreeLE R d := by
  induction f using SymmetricFunction.induction_on with
  | C r => exact ⟨0, algebraMap_mem_degreeLE r 0⟩
  | add f g hf hg =>
    obtain ⟨m, hm⟩ := hf
    obtain ⟨n, hn⟩ := hg
    exact ⟨max m n, (degreeLE R _).add_mem
      (degreeLE_mono (le_max_left _ _) hm) (degreeLE_mono (le_max_right _ _) hn)⟩
  | mul_e f i hf =>
    obtain ⟨d, hd⟩ := hf
    exact ⟨d + i, mul_mem_degreeLE hd (e_mem_degreeLE i)⟩

section Examples

attribute [local irreducible] SymmetricFunction

example : IsHomogeneous (e (R := R) 1 ^ 2 + e 2) 2 :=
  ((isHomogeneous_e 1).pow 2).add (isHomogeneous_e 2)

example : e (R := R) 0 + e 3 ∈ degreeLE R 3 :=
  (degreeLE R 3).add_mem (degreeLE_mono (Nat.zero_le 3) (e_mem_degreeLE 0))
    (e_mem_degreeLE 3)

example [Subsingleton R] (f : SymmetricFunction R) (d : ℕ) : IsHomogeneous f d := by
  unfold IsHomogeneous
  rw [show polynomialEquiv R f = 0 from Subsingleton.elim _ _]
  exact MvPolynomial.isWeightedHomogeneous_zero R _ d

end Examples

end

end SymmetricFunction
