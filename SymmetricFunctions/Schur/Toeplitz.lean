import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Finite upper triangular matrices of formal coefficients

The cutoff is finite. Matrix multiplication is justified by the bijection from
an interval of intermediate indices to a finite coefficient antidiagonal.
-/

namespace SymmetricFunctions

noncomputable section
open scoped BigOperators

variable {A : Type*} [CommRing A]

/-- Upper triangular coefficient matrix. The guard is essential below the diagonal. -/
def upperToeplitz (N : ℕ) (F : PowerSeries A) : Matrix (Fin N) (Fin N) A :=
  fun i j => if i ≤ j then PowerSeries.coeff (j.val - i.val) F else 0

@[simp] theorem upperToeplitz_apply_le (N : ℕ) (F : PowerSeries A)
    {i j : Fin N} (hij : i ≤ j) :
    upperToeplitz N F i j = PowerSeries.coeff (j.val - i.val) F := ite_eq_left hij

theorem upperToeplitz_apply_gt (N : ℕ) (F : PowerSeries A)
    {i j : Fin N} (hij : j < i) : upperToeplitz N F i j = 0 := ite_eq_right (not_le.mpr hij)

@[simp] theorem upperToeplitz_mul (N : ℕ) (F G : PowerSeries A) :
    upperToeplitz N (F * G) = upperToeplitz N F * upperToeplitz N G := by
  classical
  ext i j
  by_cases hij : i ≤ j
  · rw [upperToeplitz_apply_le N _ hij, PowerSeries.coeff_mul, Matrix.mul_apply]
    symm
    calc
      _ = ∑ k ∈ Finset.univ.filter (fun k : Fin N => i ≤ k ∧ k ≤ j),
          PowerSeries.coeff (k.val - i.val) F * PowerSeries.coeff (j.val - k.val) G := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hik : i ≤ k <;> by_cases hkj : k ≤ j <;>
          simp [upperToeplitz, hik, hkj]
      _ = _ := by
        apply Finset.sum_bij (fun k _ => (k.val - i.val, j.val - k.val))
        · intro k hk
          have hk := (Finset.mem_filter.mp hk).2
          apply Finset.mem_antidiagonal.mpr
          omega
        · intro k hk l hl he
          have hk := (Finset.mem_filter.mp hk).2
          have hl := (Finset.mem_filter.mp hl).2
          apply Fin.ext
          have := congrArg Prod.fst he
          dsimp at this
          omega
        · intro ab hab
          have hab := Finset.mem_antidiagonal.mp hab
          let k : Fin N := ⟨i.val + ab.1, by omega⟩
          refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · change i.val ≤ i.val + ab.1 ∧ i.val + ab.1 ≤ j.val
            constructor <;> omega
          · dsimp [k]
            apply Prod.ext <;> dsimp <;> omega
        · intro k _
          rfl
  · rw [upperToeplitz, ite_eq_right hij, Matrix.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i ≤ k
    · have hkj : ¬ k ≤ j := fun h => hij (hik.trans h)
      simp [upperToeplitz, hkj]
    · simp [upperToeplitz, hik]

@[simp] theorem upperToeplitz_one (N : ℕ) :
    upperToeplitz N (1 : PowerSeries A) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [upperToeplitz]
  · by_cases hle : i ≤ j
    · have hne : j.val - i.val ≠ 0 := by
        have : i.val ≠ j.val := fun h => hij (Fin.ext h)
        omega
      simp [upperToeplitz, hle, PowerSeries.coeff_one, hne, hij]
    · simp [upperToeplitz, hle, hij]

/-- Formal series give finite matrices by an actual ring map. -/
def upperToeplitzHom (N : ℕ) : PowerSeries A →+* Matrix (Fin N) (Fin N) A where
  toFun := upperToeplitz N
  map_one' := upperToeplitz_one N
  map_mul' := upperToeplitz_mul N
  map_zero' := by ext i j; simp [upperToeplitz]
  map_add' F G := by ext i j; simp [upperToeplitz]; split_ifs <;> simp

/-- The determinant only sees the common diagonal coefficient. -/
theorem det_upperToeplitz (N : ℕ) (F : PowerSeries A) :
    (upperToeplitz N F).det = PowerSeries.coeff 0 F ^ N := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [upperToeplitz]
  · intro i j hij
    exact upperToeplitz_apply_gt N F hij

end
end SymmetricFunctions
