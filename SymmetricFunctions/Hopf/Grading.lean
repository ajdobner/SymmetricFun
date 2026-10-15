import SymmetricFunctions.Hopf.Basic

/-! # Connectedness and total tensor degree of the Hopf maps -/

namespace SymmetricFunction

noncomputable section

open scoped TensorProduct

variable {R : Type*} [CommRing R]

/-- The total degree-d tensor submodule, counting the degrees of both factors. -/
def tensorDegree (R : Type*) [CommRing R] (d : ℕ) :
    Submodule R (SymmetricFunction R ⊗[R] SymmetricFunction R) :=
  Submodule.span R {z | ∃ (i j : ℕ) (f g : SymmetricFunction R),
    i + j = d ∧ IsHomogeneous f i ∧ IsHomogeneous g j ∧ z = f ⊗ₜ[R] g}

theorem tmul_mem_tensorDegree {f g : SymmetricFunction R} {i j : ℕ}
    (hf : IsHomogeneous f i) (hg : IsHomogeneous g j) :
    f ⊗ₜ[R] g ∈ tensorDegree R (i + j) :=
  Submodule.subset_span ⟨i, j, f, g, rfl, hf, hg, rfl⟩

theorem mul_mem_tensorDegree {x y : SymmetricFunction R ⊗[R] SymmetricFunction R}
    {d k : ℕ} (hx : x ∈ tensorDegree R d) (hy : y ∈ tensorDegree R k) :
    x * y ∈ tensorDegree R (d + k) := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    rcases hx with ⟨i, j, f, g, rfl, hf, hg, rfl⟩
    rcases hy with ⟨a, b, s, t, rfl, hs, ht, rfl⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    have he : (i + a) + (j + b) = (i + j) + (a + b) := by omega
    simpa only [he] using tmul_mem_tensorDegree (hf.mul hs) (hg.mul ht)
  | zero_left y hy => simp
  | zero_right x hx => simp
  | add_left x y z hx hy hz ihx ihy =>
    simpa only [add_mul] using (tensorDegree R (d + k)).add_mem ihx ihy
  | add_right x y z hx hy hz ihy ihz =>
    simpa only [mul_add] using (tensorDegree R (d + k)).add_mem ihy ihz
  | smul_left r x y hx hy ih =>
    simpa only [smul_mul_assoc] using (tensorDegree R (d + k)).smul_mem r ih
  | smul_right r x y hx hy ih =>
    simpa only [mul_smul_comm] using (tensorDegree R (d + k)).smul_mem r ih

instance : SetLike.GradedMonoid (tensorDegree R) where
  one_mem := by
    change (1 : SymmetricFunction R) ⊗ₜ[R] 1 ∈ tensorDegree R 0
    exact tmul_mem_tensorDegree (i := 0) (j := 0)
      (isHomogeneous_one (R := R)) (isHomogeneous_one (R := R))
  mul_mem := by intro i j x y hx hy; exact mul_mem_tensorDegree (R := R) hx hy

/-- Substitution into graded submodules respects the weight of every polynomial monomial. -/
private theorem weighted_aeval_mem {σ A : Type*} [CommRing A] [Algebra R A]
    (G : ℕ → Submodule R A) [SetLike.GradedMonoid G] {w : σ → ℕ}
    (x : σ → A) (hx : ∀ i, x i ∈ G (w i)) {q : MvPolynomial σ R} {d : ℕ}
    (hq : q.IsWeightedHomogeneous w d) : MvPolynomial.aeval x q ∈ G d := by
  classical
  induction hq using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simpa using (G d).add_mem ihp ihq
  | monomial a r ha =>
    rw [MvPolynomial.aeval_monomial]
    have hp := SetLike.prod_pow_mem_graded G w x a (fun i (_ : i ∈ a.support) => hx i)
    change a.prod (fun i n => x i ^ n) ∈ G (a.weight w) at hp
    rw [ha] at hp
    simpa only [Algebra.smul_def] using (G d).smul_mem r hp

/-- Comultiplication preserves the sum of the degrees in the two tensor factors. -/
theorem comultiplication_mem_tensorDegree {f : SymmetricFunction R} {d : ℕ}
    (hf : IsHomogeneous f d) : comultiplication f ∈ tensorDegree R d := by
  change MvPolynomial.aeval (fun n : ℕ+ =>
      ∑ ij ∈ Finset.antidiagonal (n : ℕ), e ij.1 ⊗ₜ[R] e ij.2)
        (polynomialEquiv R f) ∈ tensorDegree R d
  apply weighted_aeval_mem (tensorDegree R) _ _ hf
  intro n
  apply (tensorDegree R n).sum_mem
  intro ij hij
  have ht := tmul_mem_tensorDegree (isHomogeneous_e (R := R) ij.1) (isHomogeneous_e ij.2)
  simpa only [Finset.mem_antidiagonal.mp hij] using ht

/-- The counit is the constant coefficient in the elementary presentation. -/
theorem counit_eq_coeff_zero (f : SymmetricFunction R) :
    counit f = (polynomialEquiv R f).coeff 0 := by
  simp [counit, eval, MvPolynomial.constantCoeff_eq]

/-- The counit vanishes in every positive homogeneous degree. -/
theorem counit_eq_zero_of_homogeneous {f : SymmetricFunction R} {d : ℕ}
    (hf : IsHomogeneous f d) (hd : d ≠ 0) : counit f = 0 := by
  rw [counit_eq_coeff_zero]
  exact hf.coeff_eq_zero 0 (by simpa using hd.symm)

/-- The degree-zero piece is exactly the coefficient ring, including for the zero ring. -/
def degreeZeroEquiv (R : Type*) [CommRing R] : R ≃ₗ[R] homogeneousSubmodule R 0 where
  toFun r := ⟨algebraMap R (SymmetricFunction R) r, isHomogeneous_algebraMap r⟩
  invFun f := counit f.val
  left_inv r := by simp
  right_inv f := by
    apply Subtype.ext
    obtain ⟨r, hr⟩ := (isHomogeneous_zero_iff f.val).mp f.property
    simp [hr]
  map_add' r s := by apply Subtype.ext; simp
  map_smul' r s := by apply Subtype.ext; simp [Algebra.smul_def]

@[simp] theorem degreeZeroEquiv_apply (r : R) :
    (degreeZeroEquiv R r : SymmetricFunction R) = algebraMap R (SymmetricFunction R) r := rfl

@[simp] theorem degreeZeroEquiv_symm_apply (f : homogeneousSubmodule R 0) :
    (degreeZeroEquiv R).symm f = counit f.val := rfl

/-- The antipode preserves the symmetric-function grading. -/
theorem IsHomogeneous.antipode {f : SymmetricFunction R} {d : ℕ}
    (hf : IsHomogeneous f d) : IsHomogeneous (antipode f) d :=
  isHomogeneous_eval _ (fun i => (isHomogeneous_h (R := R) i).smul _) hf

end

end SymmetricFunction
