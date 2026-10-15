import LambdaRing.Polynomial.Operations
import LambdaRing.Hom

/-! # Naturality under monomial and zero substitutions -/

noncomputable section

namespace LambdaRing.Polynomial

open MvPolynomial

variable {σ τ : Type*}

/-- Zero or a monomial with coefficient one. Such elements behave as line elements. -/
def IsLineMonomial (f : MvPolynomial σ ℤ) : Prop := f = 0 ∨ ∃ m, f = monomial m 1

@[simp] theorem isLineMonomial_zero : IsLineMonomial (0 : MvPolynomial σ ℤ) := Or.inl rfl
@[simp] theorem isLineMonomial_one : IsLineMonomial (1 : MvPolynomial σ ℤ) :=
  Or.inr ⟨0, MvPolynomial.one_def⟩
@[simp] theorem isLineMonomial_X (i : σ) : IsLineMonomial (X i : MvPolynomial σ ℤ) :=
  Or.inr ⟨Finsupp.single i 1, rfl⟩

theorem IsLineMonomial.mul {f g : MvPolynomial σ ℤ}
    (hf : IsLineMonomial f) (hg : IsLineMonomial g) : IsLineMonomial (f * g) := by
  rcases hf with rfl | ⟨m, rfl⟩
  · simp
  rcases hg with rfl | ⟨n, rfl⟩
  · simp
  exact Or.inr ⟨m + n, by rw [monomial_mul_monomial, one_mul]⟩

theorem IsLineMonomial.pow {f : MvPolynomial σ ℤ} (hf : IsLineMonomial f) (n : ℕ) :
    IsLineMonomial (f ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact ih.mul hf

theorem isLineMonomial_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ)
    (hf : ∀ i ∈ s, IsLineMonomial (f i)) : IsLineMonomial (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- A substitution sends each variable to zero or a coefficient-one monomial. -/
def IsMonomialSubstitution (φ : MvPolynomial σ ℤ →+* MvPolynomial τ ℤ) : Prop :=
  ∀ i, IsLineMonomial (φ (X i))

theorem IsMonomialSubstitution.monomial {φ : MvPolynomial σ ℤ →+* MvPolynomial τ ℤ}
    (hφ : IsMonomialSubstitution φ) (m : σ →₀ ℕ) :
    IsLineMonomial (φ (monomial m 1)) := by
  classical
  rw [MvPolynomial.monomial_eq, C_1, one_mul]
  simp only [Finsupp.prod, map_prod, map_pow]
  exact isLineMonomial_prod _ _ (fun i _ => (hφ i).pow _)

theorem IsLineMonomial.totalUnit {f : MvPolynomial σ ℤ} (hf : IsLineMonomial f) :
    totalUnit f = lineUnit f := by
  rcases hf with rfl | ⟨m, rfl⟩ <;> simp

private theorem monomial_eq_zsmul_one (m : σ →₀ ℕ) (a : ℤ) :
    monomial m a = a • monomial m (1 : ℤ) := by
  rw [← map_zsmul]
  simp

/-- Total exterior powers commute with every monomial or zero substitution. -/
theorem totalUnit_natural (φ : MvPolynomial σ ℤ →+* MvPolynomial τ ℤ)
    (hφ : IsMonomialSubstitution φ) (f : MvPolynomial σ ℤ) :
    Units.map (PowerSeries.map φ).toMonoidHom (totalUnit f) = totalUnit (φ f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [totalUnit_monomial, map_zpow, map_lineUnit, monomial_eq_zsmul_one m a,
      map_zsmul, totalUnit_zsmul, (hφ.monomial m).totalUnit]
  | add f g hf hg => rw [totalUnit_add, map_mul, hf, hg, map_add, totalUnit_add]

/-- Coefficient form of monomial-substitution naturality. -/
theorem operation_natural (φ : MvPolynomial σ ℤ →+* MvPolynomial τ ℤ)
    (hφ : IsMonomialSubstitution φ) (k : ℕ) (f : MvPolynomial σ ℤ) :
    φ (operation k f) = operation k (φ f) := by
  have h := congrArg (fun u : (PowerSeries (MvPolynomial τ ℤ))ˣ =>
    PowerSeries.coeff k (u : PowerSeries (MvPolynomial τ ℤ))) (totalUnit_natural φ hφ f)
  exact h

/-- Monomial substitutions packaged as lambda-preserving ring homomorphisms. -/
def monomialHom (φ : MvPolynomial σ ℤ →+* MvPolynomial τ ℤ)
    (hφ : IsMonomialSubstitution φ) : LambdaRingHom (MvPolynomial σ ℤ) (MvPolynomial τ ℤ) :=
  { φ with map_lambda' := operation_natural φ hφ }

@[simp] theorem monomialHom_apply (φ : MvPolynomial σ ℤ →+* MvPolynomial τ ℤ)
    (hφ : IsMonomialSubstitution φ) (f : MvPolynomial σ ℤ) : monomialHom φ hφ f = φ f := rfl

/-- Renaming need not be injective. Identifying variables also preserves operations. -/
theorem operation_rename (r : σ → τ) (k : ℕ) (f : MvPolynomial σ ℤ) :
    rename r (operation k f) = operation k (rename r f) :=
  operation_natural (rename r).toRingHom (by intro i; simp) k f

/-- Explicit variable deletion, including deleting every variable. -/
theorem operation_setZero (keep : σ → Prop) [DecidablePred keep]
    (k : ℕ) (f : MvPolynomial σ ℤ) :
    aeval (fun i => if keep i then X i else (0 : MvPolynomial σ ℤ)) (operation k f) =
      operation k (aeval (fun i => if keep i then X i else (0 : MvPolynomial σ ℤ)) f) := by
  apply operation_natural
  intro i
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
  split <;> simp

end LambdaRing.Polynomial
