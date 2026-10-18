module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Integer partitions

`IntegerPartition` packages a size together with a partition of that size. It is the
index type for a basis assembled from bases indexed by `Nat.Partition n`.

`IntegerPartition.ofMultiset` removes zero entries from a multiset of natural numbers.
`IntegerPartition.ofFn` constructs a partition from a weak composition `Fin k → ℕ`,
forgetting the order and removing zero entries.
-/

@[expose] public section

/-- An integer partition of arbitrary size. -/
abbrev IntegerPartition := Σ n : ℕ, Nat.Partition n

namespace IntegerPartition

/-- The size of a partition. -/
def size (μ : IntegerPartition) : ℕ := μ.1

/-- The multiset of parts of a partition. -/
def parts (μ : IntegerPartition) : Multiset ℕ := μ.2.parts

theorem parts_pos (μ : IntegerPartition) {i : ℕ} (hi : i ∈ μ.parts) : 0 < i :=
  μ.2.parts_pos hi

@[simp]
theorem parts_sum (μ : IntegerPartition) : μ.parts.sum = μ.size :=
  μ.2.parts_sum

@[ext]
theorem ext {μ ν : IntegerPartition} (h : μ.parts = ν.parts) : μ = ν := by
  rcases μ with ⟨n, μ⟩
  rcases ν with ⟨m, ν⟩
  have hnm : n = m := μ.parts_sum.symm.trans ((congrArg Multiset.sum h).trans ν.parts_sum)
  subst m
  exact congrArg (Sigma.mk n) (Nat.Partition.ext h)

/-- Regard a partition as a partition of a specified, equal size. -/
def toPartition (μ : IntegerPartition) {n : ℕ} (h : μ.size = n) : Nat.Partition n where
  parts := μ.parts
  parts_pos := μ.parts_pos
  parts_sum := μ.parts_sum.trans h

@[simp]
theorem parts_toPartition (μ : IntegerPartition) {n : ℕ} (h : μ.size = n) :
    (μ.toPartition h).parts = μ.parts := rfl

end IntegerPartition

namespace Nat.Partition

/-- Include a partition of `n` among partitions of arbitrary size. -/
def toIntegerPartition {n : ℕ} (μ : Nat.Partition n) : IntegerPartition := ⟨n, μ⟩

@[simp]
theorem size_toIntegerPartition {n : ℕ} (μ : Nat.Partition n) :
    μ.toIntegerPartition.size = n := rfl

@[simp]
theorem parts_toIntegerPartition {n : ℕ} (μ : Nat.Partition n) :
    μ.toIntegerPartition.parts = μ.parts := rfl

@[simp]
theorem toIntegerPartition_inj {n : ℕ} {μ ν : Nat.Partition n} :
    μ.toIntegerPartition = ν.toIntegerPartition ↔ μ = ν := by
  rw [IntegerPartition.ext_iff, parts_toIntegerPartition, parts_toIntegerPartition,
    Nat.Partition.ext_iff]

end Nat.Partition

namespace IntegerPartition

@[simp]
theorem toIntegerPartition_toPartition (μ : IntegerPartition) {n : ℕ} (h : μ.size = n) :
    (μ.toPartition h).toIntegerPartition = μ := by
  apply ext
  rfl

/-- Form an integer partition from a multiset of natural numbers, removing zero entries. -/
def ofMultiset (s : Multiset ℕ) : IntegerPartition :=
  (Nat.Partition.ofMultiset s).toIntegerPartition

@[simp]
theorem parts_ofMultiset (s : Multiset ℕ) :
    (ofMultiset s).parts = s.filter (· ≠ 0) := rfl

@[simp]
theorem size_ofMultiset (s : Multiset ℕ) : (ofMultiset s).size = s.sum := rfl

/-- Form an integer partition from a weak composition,
forgetting the order and removing zero entries. -/
def ofFn {k : ℕ} (w : Fin k → ℕ) : IntegerPartition :=
  ofMultiset (List.ofFn w : Multiset ℕ)

@[simp]
theorem parts_ofFn {k : ℕ} (w : Fin k → ℕ) :
    (ofFn w).parts = (List.ofFn w : Multiset ℕ).filter (· ≠ 0) := rfl

@[simp]
theorem size_ofFn {k : ℕ} (w : Fin k → ℕ) :
    (ofFn w).size = ∑ i, w i := by
  change (List.ofFn w).sum = _
  exact List.sum_ofFn

/-- Removing a zero entry from a weak composition preserves its partition. -/
theorem ofFn_removeNth_of_eq_zero {k : ℕ} (w : Fin (k + 1) → ℕ)
    (i : Fin (k + 1)) (hi : w i = 0) :
    ofFn (i.removeNth w) = ofFn w := by
  change ofFn (fun j => w (i.succAbove j)) = ofFn w
  apply ext
  simp only [parts_ofFn, ← Fin.univ_val_map]
  rw [Fin.univ_succAbove k i]
  simp [Finset.map_val, hi, Function.comp_def]

end IntegerPartition
