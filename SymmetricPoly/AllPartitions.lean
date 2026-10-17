module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# Partitions of arbitrary size

`AllPartitions` packages a size together with a partition of that size. It is the
index type for a basis assembled from bases indexed by `Nat.Partition n`.
-/

@[expose] public section

/-- A partition together with its size. -/
abbrev AllPartitions := Σ n : ℕ, Nat.Partition n

namespace AllPartitions

/-- The size of a partition. -/
def size (μ : AllPartitions) : ℕ := μ.1

/-- The multiset of parts of a partition. -/
def parts (μ : AllPartitions) : Multiset ℕ := μ.2.parts

theorem parts_pos (μ : AllPartitions) {i : ℕ} (hi : i ∈ μ.parts) : 0 < i :=
  μ.2.parts_pos hi

@[simp]
theorem parts_sum (μ : AllPartitions) : μ.parts.sum = μ.size :=
  μ.2.parts_sum

@[ext]
theorem ext {μ ν : AllPartitions} (h : μ.parts = ν.parts) : μ = ν := by
  rcases μ with ⟨n, μ⟩
  rcases ν with ⟨m, ν⟩
  have hnm : n = m := μ.parts_sum.symm.trans ((congrArg Multiset.sum h).trans ν.parts_sum)
  subst m
  exact congrArg (Sigma.mk n) (Nat.Partition.ext h)

/-- Regard a partition as a partition of a specified, equal size. -/
def toPartition (μ : AllPartitions) {n : ℕ} (h : μ.size = n) : Nat.Partition n where
  parts := μ.parts
  parts_pos := μ.parts_pos
  parts_sum := μ.parts_sum.trans h

@[simp]
theorem parts_toPartition (μ : AllPartitions) {n : ℕ} (h : μ.size = n) :
    (μ.toPartition h).parts = μ.parts := rfl

end AllPartitions

namespace Nat.Partition

/-- Include a partition of `n` among partitions of arbitrary size. -/
def toAllPartitions {n : ℕ} (μ : Nat.Partition n) : AllPartitions := ⟨n, μ⟩

@[simp]
theorem size_toAllPartitions {n : ℕ} (μ : Nat.Partition n) :
    μ.toAllPartitions.size = n := rfl

@[simp]
theorem parts_toAllPartitions {n : ℕ} (μ : Nat.Partition n) :
    μ.toAllPartitions.parts = μ.parts := rfl

@[simp]
theorem toAllPartitions_inj {n : ℕ} {μ ν : Nat.Partition n} :
    μ.toAllPartitions = ν.toAllPartitions ↔ μ = ν := by
  rw [AllPartitions.ext_iff, parts_toAllPartitions, parts_toAllPartitions, Nat.Partition.ext_iff]

end Nat.Partition

namespace AllPartitions

@[simp]
theorem toAllPartitions_toPartition (μ : AllPartitions) {n : ℕ} (h : μ.size = n) :
    (μ.toPartition h).toAllPartitions = μ := by
  apply ext
  rfl

end AllPartitions
