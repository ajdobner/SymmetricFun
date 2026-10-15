import SymmetricFunctions.Complete
import SymmetricFunctions.Grading.Evaluation

/-! # The elementary-complete involution -/

namespace SymmetricFunction

noncomputable section

variable {R : Type*} [CommRing R]

/-- The algebra endomorphism interchanging elementary and complete generators. -/
def omegaHom : SymmetricFunction R →ₐ[R] SymmetricFunction R := eval (fun i : ℕ+ => h i)

@[simp] theorem omegaHom_e (n : ℕ) : omegaHom (e (R := R) n) = h n := by
  cases n <;> simp [omegaHom]

@[simp] theorem omegaHom_h (n : ℕ) : omegaHom (h (R := R) n) = e n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [h_succ, map_sum, e_succ_h]
      apply Finset.sum_congr rfl
      intro ij hij
      have hp := Finset.mem_antidiagonal.mp hij
      rw [map_smul, map_mul, omegaHom_e, ih ij.2 (by omega)]

theorem omegaHom_comp_self :
    (omegaHom (R := R)).comp omegaHom = AlgHom.id R (SymmetricFunction R) := by
  apply algHom_ext
  intro i
  simp

/-- The standard involution as an algebra equivalence. -/
def omega : SymmetricFunction R ≃ₐ[R] SymmetricFunction R :=
  AlgEquiv.ofAlgHom omegaHom omegaHom omegaHom_comp_self omegaHom_comp_self

theorem omega_apply (f : SymmetricFunction R) : omega f = omegaHom f := rfl

@[simp] theorem omega_e (n : ℕ) : omega (e (R := R) n) = h n := omegaHom_e n

@[simp] theorem omega_h (n : ℕ) : omega (h (R := R) n) = e n := omegaHom_h n

@[simp] theorem omega_symm : (omega (R := R)).symm = omega := rfl

@[simp] theorem omega_omega (f : SymmetricFunction R) : omega (omega f) = f :=
  DFunLike.congr_fun omegaHom_comp_self f

theorem omega_involutive : Function.Involutive (omega (R := R)) := omega_omega

theorem IsHomogeneous.omega {f : SymmetricFunction R} {d : ℕ}
    (hf : IsHomogeneous f d) : IsHomogeneous (SymmetricFunction.omega f) d :=
  isHomogeneous_eval _ (fun i => isHomogeneous_h i) hf

@[simp] theorem isHomogeneous_omega_iff {f : SymmetricFunction R} {d : ℕ} :
    IsHomogeneous (omega f) d ↔ IsHomogeneous f d :=
  ⟨fun hf => by simpa using hf.omega, fun hf => hf.omega⟩

theorem omega_mem_degreeLE {f : SymmetricFunction R} {d : ℕ}
    (hf : f ∈ degreeLE R d) : omega f ∈ degreeLE R d := by
  have hle : degreeLE R d ≤ (degreeLE R d).comap (omega (R := R)).toLinearMap := by
    refine iSup_le fun k => iSup_le fun hk => ?_
    intro g hg
    exact homogeneous_le_degreeLE hk (IsHomogeneous.omega hg)
  exact hle hf

@[simp] theorem omega_mem_degreeLE_iff {f : SymmetricFunction R} {d : ℕ} :
    omega f ∈ degreeLE R d ↔ f ∈ degreeLE R d :=
  ⟨fun hf => by simpa using omega_mem_degreeLE hf, omega_mem_degreeLE⟩

/-- Restrict omega to any homogeneous piece. -/
def omegaHomogeneous (d : ℕ) : homogeneousSubmodule R d ≃ₗ[R] homogeneousSubmodule R d where
  toFun f := ⟨omega (R := R) f.val, IsHomogeneous.omega f.property⟩
  invFun f := ⟨omega (R := R) f.val, IsHomogeneous.omega f.property⟩
  left_inv f := Subtype.ext (omega_omega f.val)
  right_inv f := Subtype.ext (omega_omega f.val)
  map_add' f g := Subtype.ext (map_add (omega (R := R)) f.val g.val)
  map_smul' r f := Subtype.ext (map_smul (omega (R := R)) r f.val)

@[simp] theorem omegaHomogeneous_apply (d : ℕ) (f : homogeneousSubmodule R d) :
    (omegaHomogeneous d f : SymmetricFunction R) = omega f := rfl

@[simp] theorem omegaHomogeneous_symm (d : ℕ) :
    (omegaHomogeneous (R := R) d).symm = omegaHomogeneous d := rfl

section Examples

attribute [local irreducible] SymmetricFunction

example : omega (e (R := R) 2) = e 1 ^ 2 - e 2 := by rw [omega_e, h_two]

example {f : SymmetricFunction R} (hf : f ∈ degreeLE R 3) : omega f ∈ degreeLE R 3 :=
  omega_mem_degreeLE hf

end Examples

end

end SymmetricFunction
