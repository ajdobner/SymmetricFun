import SymmetricFunctions.Hopf.Basic

/-! # Hopf maps commute with arbitrary coefficient homomorphisms -/

namespace SymmetricFunction

noncomputable section

open scoped TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S]

@[simp] theorem map_h (φ : R →+* S) (n : ℕ) : map φ (h (R := R) n) = h n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [h_succ, map_sum, h_succ]
      apply Finset.sum_congr rfl
      intro ij hij
      have hp := Finset.mem_antidiagonal.mp hij
      simp only [Algebra.smul_def, map_mul, map_pow, map_neg, map_one,
        map_e, ih ij.2 (by omega)]

/-- The coefficient map on tensors, changing the tensor base from R to S explicitly. -/
def tensorMap (φ : R →+* S) :
    (SymmetricFunction R ⊗[R] SymmetricFunction R) →+*
      SymmetricFunction S ⊗[S] SymmetricFunction S :=
  Algebra.TensorProduct.mapRingHom φ (map φ) (map φ)
    (by ext r; simp) (by ext r; simp)

@[simp] theorem tensorMap_tmul (φ : R →+* S) (f g : SymmetricFunction R) :
    tensorMap φ (f ⊗ₜ[R] g) = map φ f ⊗ₜ[S] map φ g := by
  simp [tensorMap]

@[simp] theorem tensorMap_algebraMap (φ : R →+* S) (r : R) :
    tensorMap φ (algebraMap R (SymmetricFunction R ⊗[R] SymmetricFunction R) r) =
      algebraMap S (SymmetricFunction S ⊗[S] SymmetricFunction S) (φ r) := by
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem comultiplication_comp_map (φ : R →+* S) :
    comultiplication.toRingHom.comp (map φ) =
      (tensorMap φ).comp comultiplication.toRingHom := by
  apply ringHom_ext
  · intro r
    simp
  · intro i
    simp

@[simp] theorem comultiplication_map (φ : R →+* S) (f : SymmetricFunction R) :
    comultiplication (map φ f) = tensorMap φ (comultiplication f) :=
  DFunLike.congr_fun (comultiplication_comp_map φ) f

theorem counit_comp_map (φ : R →+* S) :
    counit.toRingHom.comp (map φ) = φ.comp counit.toRingHom := by
  apply ringHom_ext
  · intro r
    simp
  · intro i
    simp [i.ne_zero]

@[simp] theorem counit_map (φ : R →+* S) (f : SymmetricFunction R) :
    counit (map φ f) = φ (counit f) := DFunLike.congr_fun (counit_comp_map φ) f

theorem antipode_comp_map (φ : R →+* S) :
    antipode.toRingHom.comp (map φ) = (map φ).comp antipode.toRingHom := by
  apply ringHom_ext
  · intro r
    simp
  · intro i
    simp [Algebra.smul_def]

@[simp] theorem antipode_map (φ : R →+* S) (f : SymmetricFunction R) :
    antipode (map φ f) = map φ (antipode f) := DFunLike.congr_fun (antipode_comp_map φ) f

theorem comultiplication_baseChange (a : R) (f : SymmetricFunction ℤ) :
    comultiplication (baseChange R (a ⊗ₜ[ℤ] f)) =
      a • tensorMap (Int.castRingHom R) (comultiplication f) := by
  rw [baseChange_tmul, map_smul, comultiplication_map]

theorem counit_baseChange (a : R) (f : SymmetricFunction ℤ) :
    counit (baseChange R (a ⊗ₜ[ℤ] f)) = a * ((counit (R := ℤ) f : ℤ) : R) := by
  rw [baseChange_tmul, map_smul, counit_map]
  rfl

theorem antipode_baseChange (a : R) (f : SymmetricFunction ℤ) :
    antipode (baseChange R (a ⊗ₜ[ℤ] f)) = baseChange R (a ⊗ₜ[ℤ] antipode f) := by
  rw [baseChange_tmul, map_smul, antipode_map, baseChange_tmul]

end

end SymmetricFunction
