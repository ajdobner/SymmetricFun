import SymmetricFunctions.Partition
import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import Mathlib.Combinatorics.Young.SemistandardTableau

/-!
# Partition rows, containment, and tableaux

Rows are numbered from zero, in decreasing order, and padded by zeros. All shape
operations use Mathlib's Young diagrams and `Nat.Partition.conjugate`. The tableau
adapter only bounds the alphabet; it does not assert a Schur tableau formula.
-/

namespace SymmetricFunctions.Partition

open scoped BigOperators

variable {d k : ℕ}

/-- Number of positive rows. -/
def length (ξ : Nat.Partition d) : ℕ := ξ.parts.card

/-- Decreasing row lengths, with zero padding beyond the last positive row. -/
def rowLength (ξ : Nat.Partition d) (i : ℕ) : ℕ :=
  (YoungDiagram.ofPartition ξ).rowLen i

@[simp] theorem colLen_zero (ξ : Nat.Partition d) :
    (YoungDiagram.ofPartition ξ).colLen 0 = length ξ := by
  rw [← YoungDiagram.length_rowLens, YoungDiagram.rowLens_ofPartition_eq_sort_parts]
  simp [length]

theorem rowLength_antitone (ξ : Nat.Partition d) : Antitone (rowLength ξ) :=
  fun i j hij => YoungDiagram.rowLen_anti _ i j hij

@[simp] theorem rowLength_pos_iff (ξ : Nat.Partition d) (i : ℕ) :
    0 < rowLength ξ i ↔ i < length ξ := by
  rw [rowLength, ← YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_colLen,
    colLen_zero]

theorem rowLength_eq_zero (ξ : Nat.Partition d) {i : ℕ} (hi : length ξ ≤ i) :
    rowLength ξ i = 0 := by
  have := (rowLength_pos_iff ξ i).not
  omega

/-- The row interface agrees with the sorted multiset of parts. -/
theorem rowLength_eq_getElem_sort (ξ : Nat.Partition d) (i : ℕ)
    (hi : i < length ξ) :
    rowLength ξ i = (ξ.parts.sort (· ≥ ·))[i]'(by simpa [length] using hi) := by
  have h := @YoungDiagram.get_rowLens (YoungDiagram.ofPartition ξ) i
    (by simpa only [YoungDiagram.length_rowLens, colLen_zero] using hi)
  simpa only [rowLength, YoungDiagram.rowLens_ofPartition_eq_sort_parts] using h.symm

/-- The sum of the positive row lengths is the size, not the number of rows. -/
theorem sum_rowLength (ξ : Nat.Partition d) :
    ∑ i ∈ Finset.range (length ξ), rowLength ξ i = d := by
  have h := YoungDiagram.sum_rowLens_eq_card (YoungDiagram.ofPartition ξ)
  rw [YoungDiagram.rowLens, colLen_zero, YoungDiagram.card_ofPartition] at h
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, Multiset.range,
    Multiset.map_coe, Multiset.sum_coe]
  exact h

/-- Any sufficient zero padding has the same total size. -/
theorem sum_rowLength_padded (ξ : Nat.Partition d) {L : ℕ} (hL : length ξ ≤ L) :
    ∑ i ∈ Finset.range L, rowLength ξ i = d := by
  calc
    _ = ∑ i ∈ Finset.range (length ξ), rowLength ξ i := by
      symm
      apply Finset.sum_subset (Finset.range_mono hL)
      intro i _ hi
      exact rowLength_eq_zero ξ (by simpa using hi)
    _ = d := sum_rowLength ξ

@[simp] theorem length_zero (ξ : Nat.Partition 0) : length ξ = 0 := by
  simp [length]

@[simp] theorem rowLength_zero (ξ : Nat.Partition 0) (i : ℕ) : rowLength ξ i = 0 :=
  rowLength_eq_zero ξ (by simp)

/-- Containment compares Young diagrams, including partitions of different sizes. -/
def Contained (μ : Nat.Partition k) (ξ : Nat.Partition d) : Prop :=
  YoungDiagram.ofPartition μ ≤ YoungDiagram.ofPartition ξ

theorem contained_iff_rowLength (μ : Nat.Partition k) (ξ : Nat.Partition d) :
    Contained μ ξ ↔ ∀ i, rowLength μ i ≤ rowLength ξ i := by
  constructor
  · intro h i
    by_contra! hi
    have hc : (i, rowLength ξ i) ∈ YoungDiagram.ofPartition μ :=
      YoungDiagram.mem_iff_lt_rowLen.mpr hi
    have := YoungDiagram.mem_iff_lt_rowLen.mp (h hc)
    exact (lt_irrefl _ this)
  · intro h c hc
    exact YoungDiagram.mem_iff_lt_rowLen.mpr
      ((YoungDiagram.mem_iff_lt_rowLen.mp hc).trans_le (h c.1))

@[simp] theorem contained_refl (ξ : Nat.Partition d) : Contained ξ ξ := le_rfl

theorem Contained.trans {a b c : ℕ} {ξ : Nat.Partition a} {μ : Nat.Partition b}
    {ν : Nat.Partition c} (h : Contained ξ μ) (h' : Contained μ ν) : Contained ξ ν :=
  le_trans h h'

@[simp] theorem zero_contained (μ : Nat.Partition 0) (ξ : Nat.Partition d) :
    Contained μ ξ := by
  rw [contained_iff_rowLength]
  simp

/-- Mathlib's partition conjugation is exactly diagram transposition. -/
@[simp] theorem ofPartition_conjugate (ξ : Nat.Partition d) :
    YoungDiagram.ofPartition ξ.conjugate = (YoungDiagram.ofPartition ξ).transpose := by
  simp [Nat.Partition.conjugate]

theorem rowLength_conjugate (ξ : Nat.Partition d) (i : ℕ) :
    rowLength ξ.conjugate i = (YoungDiagram.ofPartition ξ).colLen i := by
  simp [rowLength]

@[simp] theorem length_conjugate (ξ : Nat.Partition d) :
    length ξ.conjugate = rowLength ξ 0 := by
  rw [← colLen_zero, ofPartition_conjugate, YoungDiagram.colLen_transpose]
  rfl

@[simp] theorem contained_conjugate_iff (μ : Nat.Partition k) (ξ : Nat.Partition d) :
    Contained μ.conjugate ξ.conjugate ↔ Contained μ ξ := by
  simp [Contained]


/-- Containment cannot increase the number of cells. -/
theorem Contained.size_le {μ : Nat.Partition k} {ξ : Nat.Partition d}
    (h : Contained μ ξ) : k ≤ d := by
  simpa only [← YoungDiagram.card_ofPartition μ, ← YoungDiagram.card_ofPartition ξ]
    using Finset.card_le_card (YoungDiagram.cells_subset_iff.mpr h)

/-- Rows determine the original Mathlib partition. -/
theorem ext_rowLength {μ ξ : Nat.Partition d} (h : ∀ i, rowLength μ i = rowLength ξ i) :
    μ = ξ := by
  have hd : YoungDiagram.ofPartition μ = YoungDiagram.ofPartition ξ :=
    le_antisymm ((contained_iff_rowLength μ ξ).mpr (fun i => (h i).le))
      ((contained_iff_rowLength ξ μ).mpr (fun i => (h i).ge))
  exact (YoungDiagram.equivPartition.symm.injective (Subtype.ext hd))

@[simp] theorem length_indiscrete {n : ℕ} (hn : n ≠ 0) :
    length (Nat.Partition.indiscrete n) = 1 := by
  simp [length, Nat.Partition.indiscrete_parts hn]

/-- A one-row partition, including the empty case at size zero. -/
@[simp] theorem rowLength_indiscrete (n i : ℕ) :
    rowLength (Nat.Partition.indiscrete n) i = if i = 0 then n else 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  by_cases hi : i = 0
  · subst i
    rw [rowLength_eq_getElem_sort _ 0 (by simp [length_indiscrete hn])]
    simp [Nat.Partition.indiscrete_parts hn]
  · rw [rowLength_eq_zero _ (by simpa [length_indiscrete hn] using Nat.one_le_iff_ne_zero.mpr hi)]
    simp [hi]

/-- Conjugating a one-row partition gives a column of the same height. -/
@[simp] theorem rowLength_indiscrete_conjugate (n i : ℕ) :
    rowLength (Nat.Partition.indiscrete n).conjugate i = if i < n then 1 else 0 := by
  have hm (j : ℕ) : j < rowLength (Nat.Partition.indiscrete n).conjugate i ↔
      j = 0 ∧ i < n := by
    rw [rowLength, ← YoungDiagram.mem_iff_lt_rowLen, ofPartition_conjugate,
      YoungDiagram.mem_transpose, YoungDiagram.mem_iff_lt_rowLen]
    change i < rowLength (Nat.Partition.indiscrete n) j ↔ _
    rw [rowLength_indiscrete]
    split_ifs with hj <;> simp_all
  by_cases hi : i < n
  · have h0 := (hm 0).mpr ⟨rfl, hi⟩
    have h1 := (hm 1).not
    simp only [hi, and_true, one_ne_zero, not_false_eq_true, iff_true] at h1
    simp only [hi, ite_true]
    omega
  · have h0 := (hm 0).not
    simp only [hi, and_false, not_false_eq_true, iff_true] at h0
    simp only [hi, ite_false]
    omega

/-- A finite alphabet on Mathlib's semistandard tableaux. Entries outside the
shape are already zero by the underlying tableau structure. -/
abbrev FiniteTableau (ξ : Nat.Partition d) (N : ℕ) :=
  {T : SemistandardYoungTableau (YoungDiagram.ofPartition ξ) //
    ∀ i j, (i, j) ∈ YoungDiagram.ofPartition ξ → T i j < N}

end SymmetricFunctions.Partition
