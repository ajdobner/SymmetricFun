module

public import SymmetricFun.Partition.IntegerPartition
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.List.GetD
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Parts in decreasing order

`IntegerPartition.part μ i` is the `i`th largest part, indexed from zero and padded
with zeros. This gives a numerical description of partitions without Young diagrams.
-/

@[expose] public section

namespace IntegerPartition

/-- The empty partition. -/
def empty : IntegerPartition := ⟨0, ⟨0, by simp, rfl⟩⟩

@[simp]
theorem size_empty : empty.size = 0 := rfl

@[simp]
theorem parts_empty : empty.parts = 0 := rfl

@[simp]
theorem ofMultiset_zero : ofMultiset 0 = empty := by
  apply ext
  simp

/-- The `i`th largest part, indexed from zero, or zero past the end. -/
def part (μ : IntegerPartition) (i : ℕ) : ℕ :=
  (μ.parts.sort (· ≥ ·)).getD i 0

@[simp]
theorem part_empty (i : ℕ) : empty.part i = 0 := by
  simp [part]

private theorem getD_filter_ne_zero (l : List ℕ) (h : l.Pairwise (· ≥ ·)) (i : ℕ) :
    (l.filter (· != 0)).getD i 0 = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.pairwise_cons.mp h
    by_cases hz : a = 0
    · subst a
      have he : l = List.replicate l.length 0 :=
        List.eq_replicate_iff.mpr ⟨rfl, fun b hb => Nat.eq_zero_of_le_zero (ha b hb)⟩
      rw [he]
      cases i <;> simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split_ifs <;> rfl
    · cases i with
      | zero => simp [hz]
      | succ i => simpa [hz] using ih hl i

/-- Constructing a partition from a decreasing list preserves its zero-padded entries. -/
theorem part_ofMultiset_of_pairwise (l : List ℕ) (h : l.Pairwise (· ≥ ·)) (i : ℕ) :
    (ofMultiset (l : Multiset ℕ)).part i = l.getD i 0 := by
  simp only [part, parts_ofMultiset, Multiset.filter_coe, Multiset.coe_sort]
  rw [List.mergeSort_eq_self (· ≥ ·) (h.filter _)]
  exact getD_filter_ne_zero _ h i

/-- Constructing a partition from a decreasing weak composition preserves its
zero-padded entries. -/
theorem part_ofFn_of_antitone {k : ℕ} (w : Fin k → ℕ) (hw : Antitone w) (i : ℕ) :
    (ofFn w).part i = (List.ofFn w).getD i 0 :=
  part_ofMultiset_of_pairwise _ (List.pairwise_ofFn.mpr fun _ _ h => hw h.le) i

theorem part_eq_zero_of_card_le (μ : IntegerPartition) {i : ℕ} (hi : μ.parts.card ≤ i) :
    μ.part i = 0 :=
  List.getD_eq_default _ _ (by simpa using hi)

theorem part_pos_iff (μ : IntegerPartition) (i : ℕ) : 0 < μ.part i ↔ i < μ.parts.card := by
  constructor
  · intro h
    by_contra hi
    rw [μ.part_eq_zero_of_card_le (by omega)] at h
    omega
  · intro hi
    unfold part
    rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    exact μ.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp (List.getElem_mem _))

theorem part_antitone (μ : IntegerPartition) : Antitone μ.part := by
  intro i j hij
  by_cases hj : j < μ.parts.card
  · by_cases h : i = j
    · subst j
      exact le_rfl
    · have hi : i < μ.parts.card := lt_of_le_of_lt hij hj
      unfold part
      rw [List.getD_eq_getElem _ _ (by simpa using hj),
        List.getD_eq_getElem _ _ (by simpa using hi)]
      exact List.pairwise_iff_getElem.mp (Multiset.pairwise_sort μ.parts (· ≥ ·))
        i j _ _ (lt_of_le_of_ne hij h)
  · rw [μ.part_eq_zero_of_card_le (by omega)]
    exact Nat.zero_le _

/-- Summing sufficiently many padded parts recovers the size. -/
theorem sum_part (μ : IntegerPartition) {k : ℕ} (hk : μ.parts.card ≤ k) :
    ∑ i ∈ Finset.range k, μ.part i = μ.size := by
  have hsum : ∑ i ∈ Finset.range μ.parts.card, μ.part i = μ.size := by
    rw [← Multiset.length_sort (s := μ.parts) (· ≥ ·), ← Fin.sum_univ_eq_sum_range]
    simp only [part, List.getD_eq_getElem _ _ (Fin.is_lt _)]
    rw [← List.sum_ofFn, List.ofFn_getElem, ← Multiset.sum_coe, Multiset.sort_eq,
      μ.parts_sum]
  rw [← hsum]
  symm
  apply Finset.sum_subset (Finset.range_mono hk)
  intro i _ hi
  exact μ.part_eq_zero_of_card_le (by simpa using hi)

/-- The padded sequence of parts determines a partition. -/
theorem part_injective : Function.Injective part := by
  intro μ ν h
  have hc : μ.parts.card = ν.parts.card := by
    apply Nat.le_antisymm
    · by_contra hn
      have hp := (μ.part_pos_iff ν.parts.card).mpr (by omega)
      rw [congrFun h, ν.part_eq_zero_of_card_le le_rfl] at hp
      omega
    · by_contra hn
      have hp := (ν.part_pos_iff μ.parts.card).mpr (by omega)
      rw [← congrFun h, μ.part_eq_zero_of_card_le le_rfl] at hp
      omega
  apply IntegerPartition.ext
  have hl : μ.parts.sort (· ≥ ·) = ν.parts.sort (· ≥ ·) := by
    apply List.ext_getElem (by simpa using hc)
    intro i hi hj
    simpa only [part, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
      using congrFun h i
  simpa using congrArg (fun l : List ℕ => (l : Multiset ℕ)) hl

theorem size_le_size_of_part_le {μ ν : IntegerPartition}
    (h : ∀ i, μ.part i ≤ ν.part i) : μ.size ≤ ν.size := by
  rw [← μ.sum_part (Nat.le_max_left μ.parts.card ν.parts.card),
    ← ν.sum_part (Nat.le_max_right μ.parts.card ν.parts.card)]
  exact Finset.sum_le_sum fun i _ => h i

theorem card_le_card_of_part_le {μ ν : IntegerPartition}
    (h : ∀ i, μ.part i ≤ ν.part i) : μ.parts.card ≤ ν.parts.card := by
  by_contra hn
  have hp := (μ.part_pos_iff ν.parts.card).mpr (by omega)
  have hle := h ν.parts.card
  rw [ν.part_eq_zero_of_card_le le_rfl] at hle
  omega

/-- Inclusion of parts and equality of sizes force equality. -/
theorem eq_of_part_le_of_size_eq {μ ν : IntegerPartition}
    (h : ∀ i, μ.part i ≤ ν.part i) (hs : μ.size = ν.size) : μ = ν := by
  apply part_injective
  funext i
  let k := max μ.parts.card ν.parts.card
  by_cases hi : i < k
  · have hsum : ∑ j ∈ Finset.range k, μ.part j = ∑ j ∈ Finset.range k, ν.part j := by
      rw [μ.sum_part (Nat.le_max_left _ _), ν.sum_part (Nat.le_max_right _ _), hs]
    exact (Finset.sum_eq_sum_iff_of_le (fun j _ => h j)).mp hsum i
      (Finset.mem_range.mpr hi)
  · rw [μ.part_eq_zero_of_card_le (by dsimp [k] at hi; omega),
      ν.part_eq_zero_of_card_le (by dsimp [k] at hi; omega)]

@[simp]
theorem size_eq_zero_iff {μ : IntegerPartition} : μ.size = 0 ↔ μ = empty := by
  constructor
  · intro h
    exact (eq_of_part_le_of_size_eq (μ := empty) (ν := μ) (fun i => by simp) h.symm).symm
  · rintro rfl
    rfl

@[simp]
theorem ofFn_zero {k : ℕ} : ofFn (0 : Fin k → ℕ) = empty := by
  apply size_eq_zero_iff.mp
  simp

/-- Retain the `k` largest parts of a partition. -/
def take (μ : IntegerPartition) (k : ℕ) : IntegerPartition :=
  ofMultiset ((μ.parts.sort (· ≥ ·)).take k : Multiset ℕ)

@[simp]
theorem part_take (μ : IntegerPartition) (k i : ℕ) :
    (μ.take k).part i = if i < k then μ.part i else 0 := by
  rw [take, part_ofMultiset_of_pairwise _
    (Multiset.pairwise_sort μ.parts (· ≥ ·)).take]
  by_cases h : i < k
  · simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h, h, part]
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem parts_card_take_le (μ : IntegerPartition) (k : ℕ) :
    (μ.take k).parts.card ≤ k := by
  by_contra h
  have hp := ((μ.take k).part_pos_iff k).mpr (by omega)
  simp at hp

theorem size_take (μ : IntegerPartition) (k : ℕ) :
    (μ.take k).size = ∑ i ∈ Finset.range k, μ.part i := by
  rw [← (μ.take k).sum_part (μ.parts_card_take_le k)]
  exact Finset.sum_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]

@[simp]
theorem take_zero (μ : IntegerPartition) : μ.take 0 = empty := by
  simp [take]

theorem take_eq_self (μ : IntegerPartition) {k : ℕ} (hk : μ.parts.card ≤ k) :
    μ.take k = μ := by
  apply part_injective
  funext i
  by_cases hi : i < k
  · simp [hi]
  · simp [hi, μ.part_eq_zero_of_card_le (i := i) (by omega)]

/-- There are only finitely many partitions of bounded size. -/
instance finite_size_le (n : ℕ) : Finite {μ : IntegerPartition // μ.size ≤ n} := by
  let f : {μ : IntegerPartition // μ.size ≤ n} → Σ m : Fin (n + 1), Nat.Partition m :=
    fun μ => ⟨⟨μ.val.size, Nat.lt_succ_of_le μ.property⟩, μ.val.2⟩
  apply Finite.of_injective f
  intro μ ν h
  apply Subtype.ext
  apply IntegerPartition.ext
  exact congrArg (fun p : Σ m : Fin (n + 1), Nat.Partition m => p.2.parts) h

end IntegerPartition

namespace Nat.Partition

@[simp]
theorem toIntegerPartition_zero (μ : Partition 0) :
    μ.toIntegerPartition = IntegerPartition.empty :=
  IntegerPartition.size_eq_zero_iff.mp rfl

end Nat.Partition
