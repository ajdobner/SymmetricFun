import SymmetricFunctions.Hall
import SymmetricFunctions.Cauchy.Components

/-! # The integral Schur Cauchy kernel in total-degree completion

The size-d partition sum has total degree 2*d. Its Schur/Schur and h/m
expansions agree over every commutative ring, and finite specialization is
the actual product of inverses of 1-x_i*y_j.
-/
noncomputable section
namespace SymmetricFunction
open SymmetricFunctions
open scoped TensorProduct
variable {R : Type*} [CommRing R]

/-- The monomial reconstruction dual to the homogeneous complete basis. -/
theorem sum_hall_hPart_smul_mPart {d : ℕ} (f : homogeneousSubmodule R d) :
    (∑ μ : Nat.Partition d, hall (hPart μ) f.val • mPart μ) = f.val := by
  have he := congrArg Subtype.val ((mBasis R d).sum_repr f)
  simpa only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, mBasis_apply,
    ← hall_hPart_homogeneous] using he

/-- The finite Schur/Schur kernel for partition size d. -/
def cauchySchurComponent (R : Type*) [CommRing R] (d : ℕ) :
    SymmetricFunction R ⊗[R] SymmetricFunction R :=
  ∑ μ : Nat.Partition d, schur μ ⊗ₜ[R] schur μ

open Classical in
/-- The h/m tensor represents the degree-d identity under Hall contraction. -/
theorem tensorHall_cauchyCompleteMonomialComponent (d : ℕ) (ξ μ : Σ d, Nat.Partition d) :
    tensorHall (cauchyCompleteMonomialComponent R d) (schur ξ.2 ⊗ₜ[R] schur μ.2) =
      if ξ.1 = d then hall (schur ξ.2) (schur μ.2) else 0 := by
  classical
  rw [cauchyCompleteMonomialComponent, map_sum, LinearMap.sum_apply]
  simp only [tensorHall_tmul]
  by_cases hξ : ξ.1 = d
  · rw [ite_eq_left hξ]
    let f : homogeneousSubmodule R d := ⟨schur ξ.2, by
      change IsHomogeneous (schur (R := R) ξ.2) d
      simpa only [hξ] using isHomogeneous_schur (R := R) ξ.2⟩
    have he := congrArg (fun g => hall g (schur μ.2)) (sum_hall_hPart_smul_mPart f)
    simpa only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul] using he
  · rw [ite_eq_right hξ]
    apply Finset.sum_eq_zero
    intro η _
    rw [hall_eq_zero_of_degrees_ne (isHomogeneous_hPart η) (isHomogeneous_schur ξ.2)
      (Ne.symm hξ), zero_mul]

open Classical in
/-- Schur orthonormality gives the same degree-d identity tensor. -/
theorem tensorHall_cauchySchurComponent (d : ℕ) (ξ μ : Σ d, Nat.Partition d) :
    tensorHall (cauchySchurComponent R d) (schur ξ.2 ⊗ₜ[R] schur μ.2) =
      if ξ.1 = d then hall (schur ξ.2) (schur μ.2) else 0 := by
  classical
  rw [cauchySchurComponent, map_sum, LinearMap.sum_apply]
  simp only [tensorHall_tmul]
  by_cases hξ : ξ.1 = d
  · rw [ite_eq_left hξ]
    obtain ⟨k, ξ⟩ := ξ
    dsimp only at hξ
    subst k
    rw [Finset.sum_eq_single ξ]
    · rw [hall_schur_schur (⟨d, ξ⟩ : Σ d, Nat.Partition d) ⟨d, ξ⟩,
        ite_eq_left rfl, one_mul]
    · intro η _ hη
      have hn : (⟨d, η⟩ : Σ d, Nat.Partition d) ≠ ⟨d, ξ⟩ := by simpa using hη
      rw [hall_schur_schur (⟨d, η⟩ : Σ d, Nat.Partition d) ⟨d, ξ⟩,
        ite_eq_right hn, zero_mul]
    · simp
  · rw [ite_eq_right hξ]
    apply Finset.sum_eq_zero
    intro η _
    rw [hall_eq_zero_of_degrees_ne (isHomogeneous_schur η) (isHomogeneous_schur ξ.2)
      (Ne.symm hξ), zero_mul]

/-- The two classical Cauchy expansions agree integrally, before completion. -/
theorem cauchySchurComponent_eq_completeMonomial (d : ℕ) :
    cauchySchurComponent R d = cauchyCompleteMonomialComponent R d := by
  apply tensorHall_schur_ext
  intro ξ μ
  rw [tensorHall_cauchySchurComponent, tensorHall_cauchyCompleteMonomialComponent]

/-- The Schur sum has total degree 2*d, not d. -/
theorem cauchySchurComponent_mem (d : ℕ) :
    cauchySchurComponent R d ∈ tensorDegree R (2 * d) := by
  rw [cauchySchurComponent_eq_completeMonomial]
  exact cauchyCompleteMonomialComponent_mem d

/-- The Cauchy kernel in the existing total-degree completed tensor.
Odd components vanish; component 2*d is the size-d partition sum. -/
def cauchyKernel (R : Type*) [CommRing R] : CompletedTensor R := fun n =>
  ⟨if n % 2 = 0 then cauchyCompleteMonomialComponent R (n / 2) else 0, by
    split_ifs with hn
    · have he : 2 * (n / 2) = n := by omega
      simpa only [he] using cauchyCompleteMonomialComponent_mem (R := R) (n / 2)
    · exact (tensorDegree R n).zero_mem⟩

/-- Every even component is the complete/monomial partition sum. -/
@[simp] theorem component_cauchyKernel_even (d : ℕ) :
    CompletedTensor.component R (cauchyKernel R) (2 * d) =
      cauchyCompleteMonomialComponent R d := by
  change (if (2 * d) % 2 = 0 then cauchyCompleteMonomialComponent R (2 * d / 2) else 0) = _
  simp

/-- Every odd component is zero. -/
@[simp] theorem component_cauchyKernel_odd (d : ℕ) :
    CompletedTensor.component R (cauchyKernel R) (2 * d + 1) = 0 := by
  change (if (2 * d + 1) % 2 = 0 then
    cauchyCompleteMonomialComponent R ((2 * d + 1) / 2) else 0) = _
  simp

/-- The completed Cauchy identity, expressed as the Schur partition sum in every even degree. -/
theorem component_cauchyKernel_schur (d : ℕ) :
    CompletedTensor.component R (cauchyKernel R) (2 * d) =
      ∑ μ : Nat.Partition d, schur μ ⊗ₜ[R] schur μ := by
  rw [component_cauchyKernel_even, ← cauchySchurComponent_eq_completeMonomial]
  rfl

/-- The completed kernel specializes to the justified finite product alphabet formula. -/
theorem completedTensorSpecialization_cauchyKernel (M N : ℕ) :
    completedTensorSpecialization R M N (cauchyKernel R) =
      finiteCauchyProduct (Fin M) (Fin N) R := by
  have he (n : ℕ) : MvPowerSeries.homogeneousComponent n
      (completedTensorSpecialization R M N (cauchyKernel R)) =
      MvPowerSeries.homogeneousComponent n (finiteCauchyProduct (Fin M) (Fin N) R) := by
    rw [homogeneousComponent_completedTensorSpecialization]
    rcases Nat.even_or_odd n with hn | hn
    · obtain ⟨d, hd⟩ := hn
      have hd' : n = 2 * d := by omega
      rw [hd', component_cauchyKernel_even, homogeneousComponent_finiteCauchyProduct_even]
    · obtain ⟨d, hd⟩ := hn
      rw [hd, component_cauchyKernel_odd, homogeneousComponent_finiteCauchyProduct_odd, map_zero]
      rfl
  apply MvPowerSeries.ext
  intro a
  simpa only [MvPowerSeries.coeff_homogeneousComponent, ite_true] using
    congrArg (MvPowerSeries.coeff a) (he a.degree)

/-- The degree-zero Cauchy component is the tensor unit. -/
@[simp] theorem component_cauchyKernel_zero :
    CompletedTensor.component R (cauchyKernel R) 0 = 1 := by
  rw [show 0 = 2 * 0 by rfl, component_cauchyKernel_schur]
  simp
  rfl

/-- The first total-degree component vanishes. -/
@[simp] theorem component_cauchyKernel_one :
    CompletedTensor.component R (cauchyKernel R) 1 = 0 :=
  component_cauchyKernel_odd 0

/-- The first nonconstant Cauchy component has degree two and is e₁ ⊗ e₁. -/
@[simp] theorem component_cauchyKernel_two :
    CompletedTensor.component R (cauchyKernel R) 2 = e 1 ⊗ₜ[R] e 1 := by
  rw [show 2 = 2 * 1 by rfl, component_cauchyKernel_schur,
    Finset.univ_unique, Finset.sum_singleton]
  change schur (Nat.Partition.indiscrete 1) ⊗ₜ[R] schur (Nat.Partition.indiscrete 1) = _
  simp

end SymmetricFunction
