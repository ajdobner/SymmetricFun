module

public import SymmetricFun.Partition.Parts

/-!
# Interlacing partitions

`μ.Interlaces ν` means `ν.part (i + 1) ≤ μ.part i ≤ ν.part i` for every `i`.
Thus the smaller partition is on the left. In the language of diagrams this
would say that `ν / μ` is a horizontal strip; the definition and proofs here
only use the parts.

Interlacing is reflexive and antisymmetric, but is not transitive.
-/

@[expose] public section

namespace IntegerPartition

/-- `μ` interlaces `ν` when their decreasing, zero-padded parts alternate.
The smaller partition is the first argument. -/
def Interlaces (μ ν : IntegerPartition) : Prop :=
  ∀ i, ν.part (i + 1) ≤ μ.part i ∧ μ.part i ≤ ν.part i

namespace Interlaces

variable {μ ν : IntegerPartition}

theorem part_le (h : μ.Interlaces ν) (i : ℕ) : μ.part i ≤ ν.part i :=
  (h i).2

theorem next_part_le (h : μ.Interlaces ν) (i : ℕ) : ν.part (i + 1) ≤ μ.part i :=
  (h i).1

@[refl]
theorem refl (μ : IntegerPartition) : μ.Interlaces μ :=
  fun i => ⟨μ.part_antitone (Nat.le_succ i), le_rfl⟩

theorem size_le (h : μ.Interlaces ν) : μ.size ≤ ν.size :=
  size_le_size_of_part_le h.part_le

/-- An interlacing step introduces at most one additional part. -/
theorem card_le_succ (h : μ.Interlaces ν) : ν.parts.card ≤ μ.parts.card + 1 := by
  have hle := h.next_part_le μ.parts.card
  rw [μ.part_eq_zero_of_card_le le_rfl] at hle
  by_contra hn
  have hp := (ν.part_pos_iff (μ.parts.card + 1)).mpr (by omega)
  omega

theorem antisymm (h : μ.Interlaces ν) (h' : ν.Interlaces μ) : μ = ν :=
  part_injective (funext fun i => (h.part_le i).antisymm (h'.part_le i))

theorem eq_of_size_eq (h : μ.Interlaces ν) (hs : μ.size = ν.size) : μ = ν :=
  eq_of_part_le_of_size_eq h.part_le hs

theorem eq_iff_size_eq (h : μ.Interlaces ν) : μ = ν ↔ μ.size = ν.size :=
  ⟨fun h => congrArg size h, h.eq_of_size_eq⟩

end Interlaces

/-- Consecutive prefixes of a partition interlace. -/
theorem take_interlaces_take_succ (μ : IntegerPartition) (k : ℕ) :
    (μ.take k).Interlaces (μ.take (k + 1)) := by
  intro i
  simp only [part_take]
  by_cases hi : i < k
  · simp only [hi, Nat.add_lt_add_iff_right, ite_true, Nat.lt_add_right 1 hi]
    exact ⟨μ.part_antitone (Nat.le_succ i), le_rfl⟩
  · simp only [hi, Nat.add_lt_add_iff_right, ite_false]
    exact ⟨le_rfl, Nat.zero_le _⟩

/-- Only finitely many inequalities need to be checked. -/
theorem interlaces_iff_forall_lt (μ ν : IntegerPartition) :
    μ.Interlaces ν ↔ ∀ i < max μ.parts.card ν.parts.card,
      ν.part (i + 1) ≤ μ.part i ∧ μ.part i ≤ ν.part i := by
  constructor
  · intro h i _
    exact h i
  · intro h i
    by_cases hi : i < max μ.parts.card ν.parts.card
    · exact h i hi
    · rw [μ.part_eq_zero_of_card_le (by omega),
        ν.part_eq_zero_of_card_le (i := i) (by omega),
        ν.part_eq_zero_of_card_le (i := i + 1) (by omega)]
      exact ⟨le_rfl, le_rfl⟩

instance (μ ν : IntegerPartition) : Decidable (μ.Interlaces ν) :=
  decidable_of_iff (∀ i < max μ.parts.card ν.parts.card,
    ν.part (i + 1) ≤ μ.part i ∧ μ.part i ≤ ν.part i)
    (interlaces_iff_forall_lt μ ν).symm

/-- A chain can grow from the empty partition in one step precisely to a partition
with at most one part. -/
@[simp]
theorem empty_interlaces_iff (ν : IntegerPartition) :
    empty.Interlaces ν ↔ ν.parts.card ≤ 1 := by
  constructor
  · intro h
    have hz : ν.part 1 = 0 := by simpa using h.next_part_le 0
    by_contra hn
    have hp := (ν.part_pos_iff 1).mpr (by omega)
    omega
  · intro h i
    rw [ν.part_eq_zero_of_card_le (i := i + 1) (by omega), part_empty]
    exact ⟨le_rfl, Nat.zero_le _⟩

@[simp]
theorem interlaces_empty_iff (μ : IntegerPartition) :
    μ.Interlaces empty ↔ μ = empty := by
  constructor
  · intro h
    exact size_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h.size_le)
  · rintro rfl
    exact Interlaces.refl _

end IntegerPartition

namespace Nat.Partition

/-- Interlacing of partitions whose sizes need not agree. -/
abbrev Interlaces {m n : ℕ} (μ : Partition m) (ν : Partition n) : Prop :=
  μ.toIntegerPartition.Interlaces ν.toIntegerPartition

end Nat.Partition
