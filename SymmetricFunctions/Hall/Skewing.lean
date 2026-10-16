import SymmetricFunctions.Hall.Schur
import SymmetricFunctions.Hopf.Grading

/-! # Bounded adjoints of multiplication from finite coproduct contraction -/

noncomputable section
namespace SymmetricFunction
open scoped TensorProduct
variable {R : Type*} [CommRing R]

/-- Contract the right factor against a bounded function using the Hall pairing. -/
def hallContraction (f : SymmetricFunction R) :
    (SymmetricFunction R ⊗[R] SymmetricFunction R) →ₗ[R] SymmetricFunction R :=
  TensorProduct.lift ((LinearMap.lsmul R (SymmetricFunction R)).flip.compl₂ (hall f))

@[simp] theorem hallContraction_tmul (f x y : SymmetricFunction R) :
    hallContraction f (x ⊗ₜ[R] y) = hall f y • x := rfl

/-- Contracting the ordinary algebraic coproduct still produces a bounded function. -/
def skewing (f : SymmetricFunction R) : SymmetricFunction R →ₗ[R] SymmetricFunction R :=
  (hallContraction f).comp comultiplication.toLinearMap

theorem skewing_apply (f g : SymmetricFunction R) :
    skewing f g = hallContraction f (comultiplication g) := rfl

/-- Equality can be tested by all Hall pairings, over arbitrary coefficient rings. -/
theorem hall_ext_left {f g : SymmetricFunction R} (hfg : ∀ k, hall f k = hall g k) : f = g := by
  apply ext_schur_coefficients
  intro ξ
  rw [← hall_schur_right, ← hall_schur_right]
  exact hfg _

/-- The contraction is the tensor pairing with a pure tensor. -/
theorem hall_hallContraction (f h : SymmetricFunction R)
    (z : SymmetricFunction R ⊗[R] SymmetricFunction R) :
    hall (hallContraction f z) h = tensorHall z (h ⊗ₜ[R] f) := by
  induction z with
  | tmul x y =>
    rw [hallContraction_tmul, tensorHall_tmul, map_smul, LinearMap.smul_apply,
      smul_eq_mul, hall_symm f y, mul_comm]
  | add z w hz hw =>
    simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hz hw

/-- Defining adjunction: f-perp is adjoint to multiplication by f. -/
theorem hall_skewing (f g h : SymmetricFunction R) :
    hall (skewing f g) h = hall g (f * h) := by
  rw [skewing_apply, hall_hallContraction, ← hall_mul_right, mul_comm h f]

/-- The defining adjunction determines skewing uniquely. -/
theorem skewing_unique (f : SymmetricFunction R) (T : SymmetricFunction R →ₗ[R] SymmetricFunction R)
    (hT : ∀ g h, hall (T g) h = hall g (f * h)) : T = skewing f := by
  ext g
  apply hall_ext_left
  intro h
  rw [hT, hall_skewing]

@[simp] theorem skewing_one (g : SymmetricFunction R) : skewing 1 g = g := by
  apply hall_ext_left
  intro h
  rw [hall_skewing, one_mul]

@[simp] theorem skewing_zero (g : SymmetricFunction R) : skewing 0 g = 0 := by
  apply hall_ext_left
  intro h
  simp only [hall_skewing, zero_mul, map_zero, LinearMap.zero_apply]

/-- Skewing is linear also in its multiplying argument. -/
theorem skewing_add (f k g : SymmetricFunction R) :
    skewing (f + k) g = skewing f g + skewing k g := by
  apply hall_ext_left
  intro h
  simp only [hall_skewing, add_mul, map_add, LinearMap.add_apply]

theorem skewing_smul (r : R) (f g : SymmetricFunction R) : skewing (r • f) g = r • skewing f g := by
  apply hall_ext_left
  intro h
  simp only [hall_skewing, smul_mul_assoc, map_smul, LinearMap.smul_apply]

/-- Products of multiplying functions correspond to compositions of adjoints. -/
theorem skewing_mul (f k g : SymmetricFunction R) :
    skewing (f * k) g = skewing f (skewing k g) := by
  apply hall_ext_left
  intro h
  simp only [hall_skewing]
  congr 1
  ring

/-- Homogeneous skewing lowers weighted symmetric-function degree. -/
theorem isHomogeneous_skewing {a b : ℕ} {f g : SymmetricFunction R}
    (hf : IsHomogeneous f a) (hg : IsHomogeneous g b) :
    IsHomogeneous (skewing f g) (b - a) := by
  have ht := comultiplication_mem_tensorDegree hg
  change hallContraction f (comultiplication g) ∈ homogeneousSubmodule R (b - a)
  generalize hΔ : comultiplication g = z at ht ⊢
  clear hΔ
  induction ht using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, j, x, y, hij, hx, hy, rfl⟩ := hz
    rw [hallContraction_tmul]
    by_cases hja : a = j
    · have hi : i = b - a := by omega
      subst i
      exact (homogeneousSubmodule R (b - a)).smul_mem _ hx
    · rw [hall_eq_zero_of_degrees_ne hf hy hja, zero_smul]
      exact (homogeneousSubmodule R (b - a)).zero_mem
  | zero => simpa only [map_zero] using (homogeneousSubmodule R (b - a)).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (homogeneousSubmodule R (b - a)).add_mem ihx ihy
  | smul r x hx ih =>
    simpa only [map_smul] using (homogeneousSubmodule R (b - a)).smul_mem r ih

/-- Subtraction of natural degrees is supplemented by actual vanishing below degree a. -/
theorem skewing_eq_zero_of_degree_lt {a b : ℕ} {f g : SymmetricFunction R}
    (hf : IsHomogeneous f a) (hg : IsHomogeneous g b) (hba : b < a) : skewing f g = 0 := by
  have ht := comultiplication_mem_tensorDegree hg
  change hallContraction f (comultiplication g) = 0
  generalize hΔ : comultiplication g = z at ht ⊢
  clear hΔ
  induction ht using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, j, x, y, hij, hx, hy, rfl⟩ := hz
    rw [hallContraction_tmul, hall_eq_zero_of_degrees_ne hf hy (by omega), zero_smul]
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy, add_zero]
  | smul r x hx ih => rw [map_smul, ih, smul_zero]

/-- A homogeneous function expands over all partitions up to any sufficient degree bound. -/
theorem hall_schur_expansion_le {d D : ℕ} {f : SymmetricFunction R}
    (hf : IsHomogeneous f d) (hd : d ≤ D) :
    (∑ n ∈ Finset.range (D + 1), ∑ μ : Nat.Partition n, hall (schur μ) f • schur μ) = f := by
  classical
  rw [Finset.sum_eq_single d]
  · have he := sum_schurBasis_repr (⟨f, hf⟩ : homogeneousSubmodule R d)
    simp_rw [← hall_schur_homogeneous] at he
    exact he
  · intro n hn hnd
    apply Finset.sum_eq_zero
    intro μ _
    rw [hall_eq_zero_of_degrees_ne (isHomogeneous_schur μ) hf hnd, zero_smul]
  · intro hn
    exact (hn (by simp only [Finset.mem_range]; omega)).elim

/-- The right tensor factor expands in a finite range of Schur degrees. -/
theorem tensor_schur_expansion {d : ℕ}
    {z : SymmetricFunction R ⊗[R] SymmetricFunction R} (hz : z ∈ tensorDegree R d) :
    z = ∑ n ∈ Finset.range (d + 1), ∑ μ : Nat.Partition n,
      hallContraction (schur μ) z ⊗ₜ[R] schur μ := by
  classical
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, j, x, y, hij, hx, hy, rfl⟩ := hz
    have he := congrArg (fun q : SymmetricFunction R => x ⊗ₜ[R] q)
      (hall_schur_expansion_le hy (show j ≤ d by omega))
    simpa only [TensorProduct.tmul_sum, TensorProduct.tmul_smul,
      hallContraction_tmul, TensorProduct.smul_tmul] using he.symm
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib] using
      congrArg₂ (· + ·) ihx ihy
  | smul r x hx ih =>
    simpa only [map_smul, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
      Finset.smul_sum] using congrArg (r • ·) ih

end SymmetricFunction
