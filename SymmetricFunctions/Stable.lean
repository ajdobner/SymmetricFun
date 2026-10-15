import SymmetricFunctions.Finite.StableRange

/-!
# Uniformly bounded compatible symmetric polynomial families

The degree bound is existential and uniform across all alphabets. It is a
property of a family, not a chosen integer stored with that family.
-/

namespace SymmetricFunction

noncomputable section

open MvPolynomial

variable (R : Type*) [CommRing R]

/-- Compatibility under the zero-last-variable transitions. -/
def Compatible (f : ∀ N : ℕ, symmetricSubalgebra (Fin N) R) : Prop :=
  ∀ N, transition N (f (N + 1)) = f N

/-- One bound on total degree works for every alphabet size. -/
def UniformlyBounded (f : ∀ N : ℕ, symmetricSubalgebra (Fin N) R) : Prop :=
  ∃ d : ℕ, ∀ N, (f N).val.totalDegree ≤ d

/-- The subalgebra of compatible families with uniformly bounded degree. -/
def boundedStableSubalgebra : Subalgebra R (∀ N : ℕ, symmetricSubalgebra (Fin N) R) where
  carrier := {f | Compatible R f ∧ UniformlyBounded R f}
  algebraMap_mem' r := by
    constructor
    · intro N
      exact (transition (R := R) N).commutes r
    · exact ⟨0, fun N => by simp⟩
  zero_mem' := ⟨fun N => map_zero (transition N), 0, fun N => by simp⟩
  one_mem' := ⟨fun N => map_one (transition N), 0, fun N => by simp⟩
  add_mem' := by
    rintro f g ⟨hf, d, hd⟩ ⟨hg, c, hc⟩
    constructor
    · intro N
      change transition N (f (N + 1) + g (N + 1)) = f N + g N
      rw [map_add, hf N, hg N]
    · refine ⟨max d c, fun N => ?_⟩
      exact (MvPolynomial.totalDegree_add (f N).val (g N).val).trans
        (max_le_max (hd N) (hc N))
  mul_mem' := by
    rintro f g ⟨hf, d, hd⟩ ⟨hg, c, hc⟩
    constructor
    · intro N
      change transition N (f (N + 1) * g (N + 1)) = f N * g N
      rw [map_mul, hf N, hg N]
    · refine ⟨d + c, fun N => ?_⟩
      exact (MvPolynomial.totalDegree_mul (f N).val (g N).val).trans
        (Nat.add_le_add (hd N) (hc N))

/-- Bounded stable families; no degree bound is stored as mathematical data. -/
abbrev BoundedStable : Type _ := ↥(boundedStableSubalgebra R)

@[simp] theorem mem_boundedStableSubalgebra
    (f : ∀ N : ℕ, symmetricSubalgebra (Fin N) R) :
    f ∈ boundedStableSubalgebra R ↔ Compatible R f ∧ UniformlyBounded R f := Iff.rfl

theorem Compatible.eq_of_le {f g : ∀ N : ℕ, symmetricSubalgebra (Fin N) R}
    (hf : Compatible R f) (hg : Compatible R g) {N M : ℕ} (hNM : N ≤ M)
    (he : f M = g M) : f N = g N := by
  revert he
  induction M, hNM using Nat.le_induction with
  | base => exact id
  | succ M hNM ih =>
    intro he
    apply ih
    rw [← hf M, ← hg M, he]

theorem compatible_rho (f : SymmetricFunction R) : Compatible R (fun N => rho R N f) :=
  fun N => transition_rho N f

theorem uniformlyBounded_rho (f : SymmetricFunction R) :
    UniformlyBounded R (fun N => rho R N f) := by
  obtain ⟨d, hd⟩ := exists_mem_degreeLE f
  exact ⟨d, fun N => (mem_finiteDegreeLE R N d _).mp (rho_mem_finiteDegreeLE R N hd)⟩

/-- All finite specializations as one bounded compatible family. -/
def stableMap : SymmetricFunction R →ₐ[R] BoundedStable R where
  toFun f := ⟨fun N => rho R N f, compatible_rho R f, uniformlyBounded_rho R f⟩
  map_zero' := Subtype.ext (funext fun N => map_zero (rho R N))
  map_one' := Subtype.ext (funext fun N => map_one (rho R N))
  map_add' f g := Subtype.ext (funext fun N => map_add (rho R N) f g)
  map_mul' f g := Subtype.ext (funext fun N => map_mul (rho R N) f g)
  commutes' r := Subtype.ext (funext fun N => (rho R N).commutes r)

@[simp] theorem stableMap_apply (f : SymmetricFunction R) (N : ℕ) :
    (stableMap R f).val N = rho R N f := rfl

theorem stableMap_injective : Function.Injective (stableMap R) := by
  intro f g he
  obtain ⟨d, hd⟩ := exists_mem_degreeLE f
  obtain ⟨c, hc⟩ := exists_mem_degreeLE g
  apply (rho_eq_iff_of_bounds R (N := max d c) (le_max_left _ _) (le_max_right _ _) hd hc).mp
  exact congrArg (fun z : BoundedStable R => z.val (max d c)) he

/-- A lift reproduces every smaller alphabet by compatibility alone. -/
theorem rho_liftSymmetric_of_le (f : BoundedStable R) {N M : ℕ} (hNM : N ≤ M) :
    rho R N (liftSymmetric R M (f.val M)) = f.val N :=
  Compatible.eq_of_le R (compatible_rho R _) f.property.1 hNM (rho_liftSymmetric R M _)

theorem liftSymmetric_eq_of_le (f : BoundedStable R) {d N M : ℕ}
    (hd : ∀ K, (f.val K).val.totalDegree ≤ d) (hN : d ≤ N) (hNM : N ≤ M) :
    liftSymmetric R M (f.val M) = liftSymmetric R N (f.val N) := by
  have hb (K : ℕ) : liftSymmetric R K (f.val K) ∈ degreeLE R d :=
    liftSymmetric_mem_degreeLE R K ((mem_finiteDegreeLE R K d _).mpr (hd K))
  apply (rho_eq_iff_of_degreeLE R hN (hb M) (hb N)).mp
  rw [rho_liftSymmetric_of_le R f hNM, rho_liftSymmetric]

/-- A lift in any stable alphabet reproduces the entire family. -/
theorem rho_liftSymmetric_of_bound (f : BoundedStable R) {d N : ℕ}
    (hd : ∀ K, (f.val K).val.totalDegree ≤ d) (hN : d ≤ N) (M : ℕ) :
    rho R M (liftSymmetric R N (f.val N)) = f.val M := by
  have he := liftSymmetric_eq_of_le R f hd hN (le_max_left N M)
  rw [← he]
  exact rho_liftSymmetric_of_le R f (le_max_right N M)

theorem stableMap_surjective : Function.Surjective (stableMap R) := by
  intro f
  obtain ⟨d, hd⟩ := f.property.2
  refine ⟨liftSymmetric R d (f.val d), ?_⟩
  apply Subtype.ext
  funext N
  exact rho_liftSymmetric_of_bound R f hd le_rfl N

/-- The polynomial-backed algebra is exactly the uniformly bounded stable realization. -/
def stableEquiv : SymmetricFunction R ≃ₐ[R] BoundedStable R :=
  AlgEquiv.ofBijective (stableMap R) ⟨stableMap_injective R, stableMap_surjective R⟩

@[simp] theorem stableEquiv_apply (f : SymmetricFunction R) (N : ℕ) :
    (stableEquiv R f).val N = rho R N f := rfl

/-- The inverse has the same value for every valid bound and stable alphabet. -/
theorem stableEquiv_symm_eq_lift (f : BoundedStable R) {d N : ℕ}
    (hd : ∀ K, (f.val K).val.totalDegree ≤ d) (hN : d ≤ N) :
    (stableEquiv R).symm f = liftSymmetric R N (f.val N) := by
  apply (stableEquiv R).injective
  apply Subtype.ext
  funext M
  simpa using (rho_liftSymmetric_of_bound R f hd hN M).symm

/-- Explicit independence of both uniform bounds and stable alphabet sizes. -/
theorem liftSymmetric_independent (f : BoundedStable R) {d c N M : ℕ}
    (hd : ∀ K, (f.val K).val.totalDegree ≤ d) (hc : ∀ K, (f.val K).val.totalDegree ≤ c)
    (hN : d ≤ N) (hM : c ≤ M) :
    liftSymmetric R N (f.val N) = liftSymmetric R M (f.val M) := by
  rw [← stableEquiv_symm_eq_lift R f hd hN, ← stableEquiv_symm_eq_lift R f hc hM]

@[simp] theorem rho_stableEquiv_symm (f : BoundedStable R) (N : ℕ) :
    rho R N ((stableEquiv R).symm f) = f.val N :=
  congrArg (fun z : BoundedStable R => z.val N) ((stableEquiv R).apply_symm_apply f)

section Examples

attribute [local irreducible] SymmetricFunction

example : (stableEquiv R (e 0)).val 0 = 1 := by simp

example (f : BoundedStable R) : (stableEquiv R ((stableEquiv R).symm f)).val 0 = f.val 0 := by
  simp

end Examples

end

end SymmetricFunction
