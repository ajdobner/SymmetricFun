module

public import SymmetricFun.Partition.Interlacing

/-!
# The Bender–Knuth reflection of a middle partition

For `μ ≺ ν ≺ π`, the admissible interval for `ν.part j` has endpoints
`max (μ.part j) (π.part (j + 1))` and
`min (π.part j) (μ.part (j - 1))`. At `j = 0`, the upper endpoint is `π.part 0`.
Reflecting each part in this interval gives the Bender–Knuth involution.

This is the Berenstein–Kirillov toggle formula, also implemented in Sage:
https://github.com/sagemath/sage/blob/develop/src/sage/combinat/gelfand_tsetlin_patterns.py
-/

@[expose] public section

namespace IntegerPartition

/-- Lower bound on a middle part between two fixed partitions. -/
def interlacingLower (μ π : IntegerPartition) (j : ℕ) : ℕ :=
  max (μ.part j) (π.part (j + 1))

/-- Upper bound on a middle part between two fixed partitions. -/
def interlacingUpper (μ π : IntegerPartition) : ℕ → ℕ
  | 0 => π.part 0
  | j + 1 => min (μ.part j) (π.part (j + 1))

private theorem middle_bounds {μ ν π : IntegerPartition}
    (hμν : μ.Interlaces ν) (hνπ : ν.Interlaces π) (j : ℕ) :
    interlacingLower μ π j ≤ ν.part j ∧ ν.part j ≤ interlacingUpper μ π j := by
  constructor
  · exact max_le (hμν.part_le j) (hνπ.next_part_le j)
  · cases j with
    | zero => exact hνπ.part_le 0
    | succ j => exact le_min (hμν.next_part_le j) (hνπ.part_le (j + 1))

/-- Reflect a middle part in its interval of admissible values. -/
def reflectedPart (μ ν π : IntegerPartition) (j : ℕ) : ℕ :=
  interlacingLower μ π j + interlacingUpper μ π j - ν.part j

private theorem reflectedPart_bounds {μ ν π : IntegerPartition}
    (hμν : μ.Interlaces ν) (hνπ : ν.Interlaces π) (j : ℕ) :
    interlacingLower μ π j ≤ reflectedPart μ ν π j ∧
      reflectedPart μ ν π j ≤ interlacingUpper μ π j := by
  have h := middle_bounds hμν hνπ j
  dsimp [reflectedPart]
  omega

private theorem upper_le_part (μ π : IntegerPartition) (j : ℕ) :
    interlacingUpper μ π j ≤ π.part j := by
  cases j with
  | zero => exact le_rfl
  | succ j => exact min_le_right _ _

private theorem reflectedPart_antitone {μ ν π : IntegerPartition}
    (hμν : μ.Interlaces ν) (hνπ : ν.Interlaces π) :
    Antitone (reflectedPart μ ν π) := by
  apply antitone_nat_of_succ_le
  intro j
  exact (reflectedPart_bounds hμν hνπ (j + 1)).2.trans
    ((min_le_left _ _).trans ((le_max_left _ _).trans
      (reflectedPart_bounds hμν hνπ j).1))

private theorem reflectedPart_zero {μ ν π : IntegerPartition}
    (hμν : μ.Interlaces ν) (hνπ : ν.Interlaces π) (j : ℕ) (hj : π.parts.card ≤ j) :
    reflectedPart μ ν π j = 0 := by
  have h := (reflectedPart_bounds hμν hνπ j).2.trans (upper_le_part μ π j)
  rw [π.part_eq_zero_of_card_le hj] at h
  omega

/-- Reflect the middle partition, keeping its two neighbors fixed. -/
def benderKnuthMiddle (μ ν π : IntegerPartition) : IntegerPartition :=
  ofFn (fun i : Fin π.parts.card => reflectedPart μ ν π i)

theorem part_benderKnuthMiddle {μ ν π : IntegerPartition}
    (hμν : μ.Interlaces ν) (hνπ : ν.Interlaces π) (j : ℕ) :
    (benderKnuthMiddle μ ν π).part j =
      interlacingLower μ π j + interlacingUpper μ π j - ν.part j := by
  rw [benderKnuthMiddle, part_ofFn_of_antitone _
    (fun _ _ h => reflectedPart_antitone hμν hνπ h)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs with hj
  · rfl
  · simpa [reflectedPart] using (reflectedPart_zero hμν hνπ j (by omega)).symm

theorem interlaces_benderKnuthMiddle {μ ν π : IntegerPartition}
    (hμν : μ.Interlaces ν) (hνπ : ν.Interlaces π) :
    μ.Interlaces (benderKnuthMiddle μ ν π) := by
  intro j
  simp only [part_benderKnuthMiddle hμν hνπ]
  exact ⟨(reflectedPart_bounds hμν hνπ (j + 1)).2.trans (min_le_left _ _),
    (le_max_left _ _).trans (reflectedPart_bounds hμν hνπ j).1⟩

theorem benderKnuthMiddle_interlaces {μ ν π : IntegerPartition}
    (hμν : μ.Interlaces ν) (hνπ : ν.Interlaces π) :
    (benderKnuthMiddle μ ν π).Interlaces π := by
  intro j
  rw [part_benderKnuthMiddle hμν hνπ]
  exact ⟨(le_max_right _ _).trans (reflectedPart_bounds hμν hνπ j).1,
    (reflectedPart_bounds hμν hνπ j).2.trans (upper_le_part μ π j)⟩

theorem benderKnuthMiddle_involutive {μ ν π : IntegerPartition}
    (hμν : μ.Interlaces ν) (hνπ : ν.Interlaces π) :
    benderKnuthMiddle μ (benderKnuthMiddle μ ν π) π = ν := by
  apply part_injective
  funext j
  rw [part_benderKnuthMiddle (interlaces_benderKnuthMiddle hμν hνπ)
    (benderKnuthMiddle_interlaces hμν hνπ), part_benderKnuthMiddle hμν hνπ]
  have h := middle_bounds hμν hνπ j
  omega

private theorem sum_bounds (μ π : IntegerPartition) (n : ℕ) :
    (∑ j ∈ Finset.range n, interlacingLower μ π j) +
      (∑ j ∈ Finset.range (n + 1), interlacingUpper μ π j) =
      (∑ j ∈ Finset.range n, μ.part j) +
        (∑ j ∈ Finset.range (n + 1), π.part j) := by
  rw [Finset.sum_range_succ' (interlacingUpper μ π),
    Finset.sum_range_succ' π.part]
  simp only [interlacingUpper]
  rw [← Nat.add_assoc, ← Finset.sum_add_distrib, ← Nat.add_assoc,
    ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  dsimp [interlacingLower]
  omega

/-- The reflection exchanges the sizes of the two horizontal strips. -/
theorem size_benderKnuthMiddle_add {μ ν π : IntegerPartition}
    (hμν : μ.Interlaces ν) (hνπ : ν.Interlaces π) :
    (benderKnuthMiddle μ ν π).size + ν.size = μ.size + π.size := by
  let n := π.parts.card
  have hμ : μ.parts.card ≤ n :=
    (card_le_card_of_part_le hμν.part_le).trans (card_le_card_of_part_le hνπ.part_le)
  have hν : ν.parts.card ≤ n := card_le_card_of_part_le hνπ.part_le
  have ht : (benderKnuthMiddle μ ν π).parts.card ≤ n :=
    card_le_card_of_part_le (benderKnuthMiddle_interlaces hμν hνπ).part_le
  have hu : interlacingUpper μ π n = 0 := by
    have h := upper_le_part μ π n
    rw [π.part_eq_zero_of_card_le le_rfl] at h
    omega
  have hs := sum_bounds μ π n
  rw [Finset.sum_range_succ (f := interlacingUpper μ π), hu, Nat.add_zero,
    μ.sum_part hμ, π.sum_part (by dsimp [n]; omega)] at hs
  rw [← (benderKnuthMiddle μ ν π).sum_part ht, ← ν.sum_part hν,
    ← Finset.sum_add_distrib, ← hs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [part_benderKnuthMiddle hμν hνπ]
  have h := middle_bounds hμν hνπ j
  omega

end IntegerPartition
