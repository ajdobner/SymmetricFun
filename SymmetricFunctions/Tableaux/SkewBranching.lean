import SymmetricFunctions.Tableaux.Skew

/-! # Removing and restoring the largest tableau letter -/
noncomputable section
namespace SymmetricFunctions.Partition.SkewTableau
open scoped BigOperators
variable {d e n N : ℕ} {ξ : Nat.Partition d} {μ : Nat.Partition e}

/-- A skew filling is weakly increasing in the product order on its actual cells. -/
theorem entry_mono (T : SkewTableau ξ μ N) {c c' : SkewCell ξ μ}
    (h : c.val ≤ c'.val) : T.entry c ≤ T.entry c' := by
  rcases lt_or_eq_of_le h.1 with hi | hi
  · have hm : (c.val.1, c'.val.2) ∈ YoungDiagram.ofPartition ξ :=
      (YoungDiagram.ofPartition ξ).up_left_mem hi.le le_rfl (Finset.mem_sdiff.mp c'.property).1
    have hm' : (c.val.1, c'.val.2) ∉ YoungDiagram.ofPartition μ := by
      intro hh
      exact (Finset.mem_sdiff.mp c.property).2
        ((YoungDiagram.ofPartition μ).up_left_mem le_rfl h.2 hh)
    let mid : SkewCell ξ μ := ⟨(c.val.1, c'.val.2), Finset.mem_sdiff.mpr ⟨hm, hm'⟩⟩
    exact le_trans (T.row_weak c mid rfl h.2) (T.col_strict mid c' rfl hi).le
  · exact T.row_weak c c' hi h.2

/-- Keep the inner diagram and all entries below the largest letter. -/
def lowerDiagram (T : SkewTableau ξ μ (N + 1)) : YoungDiagram where
  cells := (YoungDiagram.ofPartition ξ).cells.filter fun c =>
    c ∈ YoungDiagram.ofPartition μ ∨
      ∃ hc : c ∈ (YoungDiagram.ofPartition ξ).cells \ (YoungDiagram.ofPartition μ).cells,
        (T.entry ⟨c, hc⟩).val < N
  isLowerSet := by
    intro b a hab hb
    obtain ⟨hbξ, hb⟩ := Finset.mem_filter.mp hb
    have haξ := (YoungDiagram.ofPartition ξ).up_left_mem hab.1 hab.2 hbξ
    apply Finset.mem_filter.mpr
    refine ⟨haξ, ?_⟩
    by_cases haμ : a ∈ YoungDiagram.ofPartition μ
    · exact Or.inl haμ
    · rcases hb with hbμ | ⟨hb, hlt⟩
      · exact False.elim (haμ ((YoungDiagram.ofPartition μ).up_left_mem hab.1 hab.2 hbμ))
      · have ha := Finset.mem_sdiff.mpr ⟨haξ, haμ⟩
        exact Or.inr ⟨ha, lt_of_le_of_lt (T.entry_mono (c := ⟨a, ha⟩) (c' := ⟨b, hb⟩) hab) hlt⟩

theorem lowerDiagram_le (T : SkewTableau ξ μ (N + 1)) :
    lowerDiagram T ≤ YoungDiagram.ofPartition ξ := by
  intro c hc
  exact (Finset.mem_filter.mp hc).1

theorem inner_le_lowerDiagram (T : SkewTableau ξ μ (N + 1)) :
    YoungDiagram.ofPartition μ ≤ lowerDiagram T := by
  intro c hc
  exact Finset.mem_filter.mpr ⟨T.contained hc, Or.inl hc⟩

/-- On actual skew cells, membership is exactly the strict entry bound. -/
@[simp] theorem mem_lowerDiagram_iff (T : SkewTableau ξ μ (N + 1)) (c : SkewCell ξ μ) :
    c.val ∈ lowerDiagram T ↔ (T.entry c).val < N := by
  change (c.val ∈ (YoungDiagram.ofPartition ξ).cells.filter _) ↔ _
  have hcμ : c.val ∉ YoungDiagram.ofPartition μ := (Finset.mem_sdiff.mp c.property).2
  simp only [Finset.mem_filter, (Finset.mem_sdiff.mp c.property).1, true_and, hcμ, false_or]
  constructor
  · rintro ⟨hc, hh⟩
    exact hh
  · intro hh
    exact ⟨c.property, hh⟩

/-- The intermediate shape is an existing Mathlib partition with a finite size bound. -/
def lowerShape (T : SkewTableau ξ μ (N + 1)) : Σ n : Fin (d + 1), Nat.Partition n :=
  ⟨⟨(lowerDiagram T).card, by
      apply Nat.lt_succ_of_le
      simpa only [YoungDiagram.card_ofPartition] using
        Finset.card_le_card (lowerDiagram_le T)⟩,
    (lowerDiagram T).toPartition rfl⟩

@[simp] theorem ofPartition_lowerShape (T : SkewTableau ξ μ (N + 1)) :
    YoungDiagram.ofPartition (lowerShape T).2 = lowerDiagram T :=
  YoungDiagram.ofPartition_toPartition rfl

theorem lowerShape_contained (T : SkewTableau ξ μ (N + 1)) : Contained μ (lowerShape T).2 := by
  change YoungDiagram.ofPartition μ ≤ YoungDiagram.ofPartition _
  rw [ofPartition_lowerShape]
  exact inner_le_lowerDiagram T

/-- Removed entries are all the largest letter, so no column can contain two. -/
theorem lowerShape_horizontalStrip (T : SkewTableau ξ μ (N + 1)) :
    HorizontalStrip (lowerShape T).2 ξ := by
  have hc : Contained (lowerShape T).2 ξ := by
    change YoungDiagram.ofPartition _ ≤ YoungDiagram.ofPartition ξ
    rw [ofPartition_lowerShape]
    exact lowerDiagram_le T
  apply horizontalStrip_of_column_injective hc
  intro i k j hi hi' hk hk'
  rw [ofPartition_lowerShape] at hi' hk'
  have hiμ : (i, j) ∉ YoungDiagram.ofPartition μ := fun h => hi' (inner_le_lowerDiagram T h)
  have hkμ : (k, j) ∉ YoungDiagram.ofPartition μ := fun h => hk' (inner_le_lowerDiagram T h)
  let c : SkewCell ξ μ := ⟨(i, j), Finset.mem_sdiff.mpr ⟨hi, hiμ⟩⟩
  let c' : SkewCell ξ μ := ⟨(k, j), Finset.mem_sdiff.mpr ⟨hk, hkμ⟩⟩
  have hv : (T.entry c).val = N := by
    have hn : ¬ (T.entry c).val < N := fun h => hi' ((mem_lowerDiagram_iff T c).mpr h)
    have := (T.entry c).isLt
    omega
  have hv' : (T.entry c').val = N := by
    have hn : ¬ (T.entry c').val < N := fun h => hk' ((mem_lowerDiagram_iff T c').mpr h)
    have := (T.entry c').isLt
    omega
  have he : T.entry c = T.entry c' := Fin.ext (hv.trans hv'.symm)
  rcases lt_trichotomy i k with h | h | h
  · exact False.elim ((ne_of_lt (T.col_strict c c' rfl h)) he)
  · exact h
  · exact False.elim ((ne_of_lt (T.col_strict c' c rfl h)) he.symm)

/-- A retained skew cell is an actual cell of the original filling. -/
def lowerCell (T : SkewTableau ξ μ (N + 1)) (c : SkewCell (lowerShape T).2 μ) :
    SkewCell ξ μ :=
  ⟨c.val, Finset.mem_sdiff.mpr ⟨lowerDiagram_le T (by
      have hc : c.val ∈ YoungDiagram.ofPartition (lowerShape T).2 :=
        (Finset.mem_sdiff.mp c.property).1
      simpa only [ofPartition_lowerShape] using hc), (Finset.mem_sdiff.mp c.property).2⟩⟩

theorem lowerCell_mem (T : SkewTableau ξ μ (N + 1)) (c : SkewCell (lowerShape T).2 μ) :
    (lowerCell T c).val ∈ lowerDiagram T := by
  have hc : c.val ∈ YoungDiagram.ofPartition (lowerShape T).2 :=
    (Finset.mem_sdiff.mp c.property).1
  change c.val ∈ lowerDiagram T
  simpa only [ofPartition_lowerShape] using hc

/-- Delete the largest entries; every retained entry belongs to Fin N. -/
def removeLargest (T : SkewTableau ξ μ (N + 1)) : SkewTableau (lowerShape T).2 μ N where
  contained := lowerShape_contained T
  entry c := ⟨(T.entry (lowerCell T c)).val, (mem_lowerDiagram_iff T _).mp (lowerCell_mem T c)⟩
  row_weak c c' hi hj := T.row_weak (lowerCell T c) (lowerCell T c') hi hj
  col_strict c c' hj hi := T.col_strict (lowerCell T c) (lowerCell T c') hj hi

/-- Restore a horizontal strip with the new largest letter. -/
def extendLargest {ν : Nat.Partition n} (U : SkewTableau ν μ N) (hs : HorizontalStrip ν ξ) :
    SkewTableau ξ μ (N + 1) where
  contained := le_trans U.contained hs.1
  entry c := if hc : c.val ∈ YoungDiagram.ofPartition ν then
      (U.entry ⟨c.val, Finset.mem_sdiff.mpr ⟨hc, (Finset.mem_sdiff.mp c.property).2⟩⟩).castSucc
    else Fin.last N
  row_weak c c' hi hj := by
    by_cases hc : c.val ∈ YoungDiagram.ofPartition ν <;>
      by_cases hc' : c'.val ∈ YoungDiagram.ofPartition ν
    all_goals simp only [hc, hc', dite_true, dite_false]
    · exact U.row_weak _ _ hi hj
    · exact Fin.le_last _
    · exact False.elim (hc (by
        change (c.val.1, c.val.2) ∈ YoungDiagram.ofPartition ν
        rw [hi]
        exact (YoungDiagram.ofPartition ν).up_left_mem le_rfl hj hc'))
    · exact le_rfl
  col_strict c c' hj hi := by
    by_cases hc : c.val ∈ YoungDiagram.ofPartition ν <;>
      by_cases hc' : c'.val ∈ YoungDiagram.ofPartition ν
    all_goals simp only [hc, hc', dite_true, dite_false]
    · exact U.col_strict _ _ hj hi
    · exact Fin.castSucc_lt_last _
    · exact False.elim (hc (by
        change (c.val.1, c.val.2) ∈ YoungDiagram.ofPartition ν
        rw [hj]
        exact (YoungDiagram.ofPartition ν).up_left_mem hi.le le_rfl hc'))
    · have hcξ : (c.val.1, c.val.2) ∈ YoungDiagram.ofPartition ξ :=
        (Finset.mem_sdiff.mp c.property).1
      have hc'ξ : (c'.val.1, c.val.2) ∈ YoungDiagram.ofPartition ξ := by
        rw [hj]
        exact (Finset.mem_sdiff.mp c'.property).1
      have hc'ν : (c'.val.1, c.val.2) ∉ YoungDiagram.ofPartition ν := by
        rw [hj]
        exact hc'
      exact False.elim ((ne_of_lt hi) (hs.eq_row_of_cells hcξ hc hc'ξ hc'ν))

@[simp] theorem extendLargest_entry_old {ν : Nat.Partition n} (U : SkewTableau ν μ N)
    (hs : HorizontalStrip ν ξ) (c : SkewCell ξ μ) (hc : c.val ∈ YoungDiagram.ofPartition ν) :
    (extendLargest U hs).entry c =
      (U.entry ⟨c.val, Finset.mem_sdiff.mpr ⟨hc, (Finset.mem_sdiff.mp c.property).2⟩⟩).castSucc :=
  dite_eq_left hc

@[simp] theorem extendLargest_entry_new {ν : Nat.Partition n} (U : SkewTableau ν μ N)
    (hs : HorizontalStrip ν ξ) (c : SkewCell ξ μ) (hc : c.val ∉ YoungDiagram.ofPartition ν) :
    (extendLargest U hs).entry c = Fin.last N := dite_eq_right hc

/-- Deleting and restoring the largest letter preserves every actual entry. -/
@[simp] theorem extendLargest_removeLargest (T : SkewTableau ξ μ (N + 1)) :
    extendLargest (removeLargest T) (lowerShape_horizontalStrip T) = T := by
  apply ext
  intro c
  by_cases hc : c.val ∈ YoungDiagram.ofPartition (lowerShape T).2
  · rw [extendLargest_entry_old _ _ c hc]
    rfl
  · rw [extendLargest_entry_new _ _ c hc]
    apply Fin.ext
    have hn : ¬ (T.entry c).val < N := by
      intro h
      apply hc
      rw [ofPartition_lowerShape]
      exact (mem_lowerDiagram_iff T c).mpr h
    have hh := (T.entry c).isLt
    change N = (T.entry c).val
    omega

/-- The retained diagram of an extended filling is the original intermediate diagram. -/
@[simp] theorem lowerDiagram_extendLargest {ν : Nat.Partition n} (U : SkewTableau ν μ N)
    (hs : HorizontalStrip ν ξ) :
    lowerDiagram (extendLargest U hs) = YoungDiagram.ofPartition ν := by
  apply SetLike.ext
  intro c
  by_cases hcξ : c ∈ YoungDiagram.ofPartition ξ
  · by_cases hcμ : c ∈ YoungDiagram.ofPartition μ
    · exact iff_of_true (inner_le_lowerDiagram _ hcμ) (U.contained hcμ)
    · let cell : SkewCell ξ μ := ⟨c, Finset.mem_sdiff.mpr ⟨hcξ, hcμ⟩⟩
      change cell.val ∈ lowerDiagram _ ↔ cell.val ∈ YoungDiagram.ofPartition ν
      rw [mem_lowerDiagram_iff]
      by_cases hc : cell.val ∈ YoungDiagram.ofPartition ν
      · rw [extendLargest_entry_old _ _ cell hc]
        exact iff_of_true (U.entry _).isLt hc
      · rw [extendLargest_entry_new _ _ cell hc]
        exact iff_of_false (Nat.lt_irrefl _) hc
  · exact iff_of_false (fun h => hcξ (lowerDiagram_le _ h)) (fun h => hcξ (hs.1 h))

/-- Extension remembers every old entry. -/
theorem extendLargest_injective {ν : Nat.Partition n} (hs : HorizontalStrip ν ξ) :
    Function.Injective (fun U : SkewTableau ν μ N => extendLargest U hs) := by
  intro U V h
  apply ext
  intro c
  let c' : SkewCell ξ μ := ⟨c.val, Finset.mem_sdiff.mpr
    ⟨hs.1 (Finset.mem_sdiff.mp c.property).1, (Finset.mem_sdiff.mp c.property).2⟩⟩
  have he := congrArg (fun T : SkewTableau ξ μ (N + 1) => T.entry c') h
  have hc : c'.val ∈ YoungDiagram.ofPartition ν := (Finset.mem_sdiff.mp c.property).1
  rw [extendLargest_entry_old _ _ c' hc, extendLargest_entry_old _ _ c' hc] at he
  exact Fin.castSucc_injective _ he

/-- Intermediate partitions with sizes bounded by the number of outer cells. -/
abbrev BranchShape (d : ℕ) := Σ n : Fin (d + 1), Nat.Partition n

private theorem branchShape_injective : Function.Injective
    (fun q : BranchShape d => YoungDiagram.ofPartition q.2) := by
  rintro ⟨⟨n, hn⟩, ν⟩ ⟨⟨m, hm⟩, κ⟩ h
  have hsize : n = m := by
    simpa only [YoungDiagram.card_ofPartition] using congrArg YoungDiagram.card h
  subst m
  have hp : ν = κ := ext_rowLength (fun i => congrArg (fun D : YoungDiagram => D.rowLen i) h)
  subst κ
  rfl

/-- A smaller-alphabet filling and its horizontal-strip extension datum. -/
abbrev BranchData (ξ : Nat.Partition d) (μ : Nat.Partition e) (N : ℕ) :=
  Σ q : BranchShape d, {_U : SkewTableau q.2 μ N // HorizontalStrip q.2 ξ}

def extendBranch (D : BranchData ξ μ N) : SkewTableau ξ μ (N + 1) :=
  extendLargest D.2.val D.2.property

theorem extendBranch_injective : Function.Injective (extendBranch (ξ := ξ) (μ := μ) (N := N)) := by
  rintro ⟨q, U, hU⟩ ⟨r, V, hV⟩ h
  have hq : q = r := branchShape_injective (by
    simpa only [extendBranch, lowerDiagram_extendLargest] using congrArg lowerDiagram h)
  subst r
  have hv : U = V := extendLargest_injective hU h
  subst V
  rfl

/-- The actual deletion/extension bijection, not an assumed branching identity. -/
def branchingEquiv (ξ : Nat.Partition d) (μ : Nat.Partition e) (N : ℕ) :
    SkewTableau ξ μ (N + 1) ≃ BranchData ξ μ N where
  toFun T := ⟨lowerShape T, removeLargest T, lowerShape_horizontalStrip T⟩
  invFun := extendBranch
  left_inv := extendLargest_removeLargest
  right_inv D := extendBranch_injective (extendLargest_removeLargest (extendBranch D))

/-- Split actual cells into retained cells and the newly filled horizontal strip. -/
def splitCellEquiv {ν : Nat.Partition n} (U : SkewTableau ν μ N)
    (hs : HorizontalStrip ν ξ) : SkewCell ξ μ ≃ (SkewCell ν μ ⊕ SkewCell ξ ν) where
  toFun c := if hc : c.val ∈ YoungDiagram.ofPartition ν then
      Sum.inl ⟨c.val, Finset.mem_sdiff.mpr ⟨hc, (Finset.mem_sdiff.mp c.property).2⟩⟩
    else Sum.inr ⟨c.val, Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp c.property).1, hc⟩⟩
  invFun c := match c with
    | Sum.inl c => ⟨c.val, Finset.mem_sdiff.mpr
        ⟨hs.1 (Finset.mem_sdiff.mp c.property).1, (Finset.mem_sdiff.mp c.property).2⟩⟩
    | Sum.inr c => ⟨c.val, Finset.mem_sdiff.mpr
        ⟨(Finset.mem_sdiff.mp c.property).1,
          fun h => (Finset.mem_sdiff.mp c.property).2 (U.contained h)⟩⟩
  left_inv c := by
    dsimp only
    split_ifs <;> rfl
  right_inv c := by
    cases c with
    | inl c =>
      have hc : c.val ∈ YoungDiagram.ofPartition ν := (Finset.mem_sdiff.mp c.property).1
      dsimp
      rw [dite_eq_left hc]
    | inr c =>
      have hc : c.val ∉ YoungDiagram.ofPartition ν := (Finset.mem_sdiff.mp c.property).2
      dsimp
      rw [dite_eq_right hc]

theorem extendLargest_split_left {ν : Nat.Partition n} (U : SkewTableau ν μ N)
    (hs : HorizontalStrip ν ξ) (c : SkewCell ν μ) :
    (extendLargest U hs).entry ((splitCellEquiv U hs).symm (Sum.inl c)) = (U.entry c).castSucc := by
  rw [extendLargest_entry_old]
  · rfl
  · exact (Finset.mem_sdiff.mp c.property).1

theorem extendLargest_split_right {ν : Nat.Partition n} (U : SkewTableau ν μ N)
    (hs : HorizontalStrip ν ξ) (c : SkewCell ξ ν) :
    (extendLargest U hs).entry ((splitCellEquiv U hs).symm (Sum.inr c)) = Fin.last N := by
  apply extendLargest_entry_new
  exact (Finset.mem_sdiff.mp c.property).2

/-- The exact weight split follows by multiplying over a bijection of finite cell sets. -/
theorem weight_extendLargest (R : Type*) [CommSemiring R] {ν : Nat.Partition n}
    (U : SkewTableau ν μ N) (hs : HorizontalStrip ν ξ) :
    weight R (extendLargest U hs) = MvPolynomial.rename Fin.castSucc (weight R U) *
      MvPolynomial.X (Fin.last N) ^ (d - n) := by
  classical
  have hcard : Fintype.card (SkewCell ξ ν) = d - n := by
    rw [Fintype.card_coe, Finset.card_sdiff_of_subset (YoungDiagram.cells_subset_iff.mpr hs.1)]
    simp only [YoungDiagram.card_ofPartition]
  rw [weight_eq_prod, ← (splitCellEquiv U hs).symm.prod_comp
    (fun c => (MvPolynomial.X ((extendLargest U hs).entry c) : MvPolynomial (Fin (N + 1)) R))]
  rw [Fintype.prod_sum_type]
  simp only [extendLargest_split_left, extendLargest_split_right, Finset.prod_const,
    Finset.card_univ, hcard, weight_eq_prod, map_prod, MvPolynomial.rename_X]

open Classical in
/-- Branching of genuine skew tableau sums, proved by deletion and extension of fillings. -/
theorem generatingPolynomial_succ (ξ : Nat.Partition d) (μ : Nat.Partition e) (N : ℕ)
    (R : Type*) [CommSemiring R] :
    generatingPolynomial ξ μ (N + 1) R =
      ∑ m ∈ Finset.range (d + 1), ∑ ν : Nat.Partition m,
        if HorizontalStrip ν ξ then
          MvPolynomial.rename Fin.castSucc (generatingPolynomial ν μ N R) *
            MvPolynomial.X (Fin.last N) ^ (d - m)
        else 0 := by
  classical
  calc
    generatingPolynomial ξ μ (N + 1) R =
        ∑ q : BranchShape d, ∑ U : {_U : SkewTableau q.2 μ N // HorizontalStrip q.2 ξ},
          weight R (extendLargest U.val U.property) := by
      rw [generatingPolynomial, ← (branchingEquiv ξ μ N).symm.sum_comp (weight R),
        Fintype.sum_sigma]
      rfl
    _ = ∑ q : BranchShape d, if HorizontalStrip q.2 ξ then
        MvPolynomial.rename Fin.castSucc (generatingPolynomial q.2 μ N R) *
          MvPolynomial.X (Fin.last N) ^ (d - q.1.val) else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hs : HorizontalStrip q.2 ξ
      · rw [ite_eq_left hs]
        simp_rw [weight_extendLargest]
        have hsum := (Equiv.subtypeUnivEquiv (fun _ : SkewTableau q.2 μ N => hs)).sum_comp
          (fun U => MvPolynomial.rename Fin.castSucc (weight R U) *
            MvPolynomial.X (Fin.last N) ^ (d - q.1.val))
        rw [show (∑ U : {_U : SkewTableau q.2 μ N // HorizontalStrip q.2 ξ},
          MvPolynomial.rename Fin.castSucc (weight R U.val) *
            MvPolynomial.X (Fin.last N) ^ (d - q.1.val)) =
          ∑ U : SkewTableau q.2 μ N, MvPolynomial.rename Fin.castSucc (weight R U) *
            MvPolynomial.X (Fin.last N) ^ (d - q.1.val) from hsum]
        rw [← Finset.sum_mul, ← map_sum]
        rfl
      · let : IsEmpty {_U : SkewTableau q.2 μ N // HorizontalStrip q.2 ξ} :=
          ⟨fun U => hs U.property⟩
        simp [hs]
    _ = ∑ m : Fin (d + 1), ∑ ν : Nat.Partition m,
        if HorizontalStrip ν ξ then
          MvPolynomial.rename Fin.castSucc (generatingPolynomial ν μ N R) *
            MvPolynomial.X (Fin.last N) ^ (d - m.val) else 0 := Fintype.sum_sigma _
    _ = _ := Fin.sum_univ_eq_sum_range (fun m : ℕ => ∑ ν : Nat.Partition m,
      if HorizontalStrip ν ξ then
        MvPolynomial.rename Fin.castSucc (generatingPolynomial ν μ N R) *
          MvPolynomial.X (Fin.last N) ^ (d - m) else 0) (d + 1)

end SymmetricFunctions.Partition.SkewTableau
