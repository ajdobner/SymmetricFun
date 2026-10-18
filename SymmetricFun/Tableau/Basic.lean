module

public import SymmetricFun.Partition.Interlacing
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Skew semistandard Young tableaux

A `SkewSemistandardYoungTableau k` consists of `k + 1` partitions with
interlacing consecutive terms. Its weight is the weak composition `Fin k → ℕ` of size
increments. Zero increments are allowed, and correspond to repeated partitions.

`SkewSemistandardYoungTableau.WithWeight μ ν w` fixes both endpoints and the weight. This is
a finite type of tableaux of skew shape `ν / μ`. Empty inner shape gives ordinary
semistandard tableaux. This representation uses neither cells nor Young diagrams.

The sizes are not indices of the chain's terms: using `IntegerPartition` avoids
transporting partitions along equalities between prefix sums. The sum of the
weight is related to the endpoint sizes by `innerShape_size_add_sum_weight`.
`WithWeight.appendZeroEquiv` adds or removes an unused final label by repeating
or removing the final partition.
-/

@[expose] public section

open IntegerPartition

/-- A skew semistandard Young tableau with labels in `Fin k`, represented by
the `k + 1` interlacing partitions obtained by successively adding its labels. -/
structure SkewSemistandardYoungTableau (k : ℕ) where
  /-- The partitions in the sequence. -/
  toFun : Fin (k + 1) → IntegerPartition
  /-- Consecutive partitions interlace in the direction of increasing size. -/
  interlaces : ∀ i : Fin k, (toFun i.castSucc).Interlaces (toFun i.succ)

namespace SkewSemistandardYoungTableau

variable {k : ℕ}

instance : CoeFun (SkewSemistandardYoungTableau k) (fun _ => Fin (k + 1) → IntegerPartition) :=
  ⟨toFun⟩

@[ext]
theorem ext {c d : SkewSemistandardYoungTableau k} (h : ∀ i, c i = d i) : c = d := by
  cases c
  cases d
  congr
  exact funext h

/-- The inner shape of the skew tableau. -/
def innerShape (c : SkewSemistandardYoungTableau k) : IntegerPartition := c 0

/-- The outer shape of the skew tableau. -/
def outerShape (c : SkewSemistandardYoungTableau k) : IntegerPartition := c (Fin.last k)

/-- The weak composition of successive size increments. -/
def weight (c : SkewSemistandardYoungTableau k) (i : Fin k) : ℕ :=
  (c i.succ).size - (c i.castSucc).size

theorem part_mono (c : SkewSemistandardYoungTableau k) (j : ℕ) :
    Monotone (fun i => (c i).part j) :=
  Fin.monotone_iff_le_succ.mpr fun i => (c.interlaces i).part_le j

theorem size_mono (c : SkewSemistandardYoungTableau k) : Monotone (fun i => (c i).size) :=
  Fin.monotone_iff_le_succ.mpr fun i => (c.interlaces i).size_le

theorem innerShape_size_le (c : SkewSemistandardYoungTableau k) (i : Fin (k + 1)) :
    c.innerShape.size ≤ (c i).size :=
  c.size_mono (Fin.zero_le i)

theorem size_le_outerShape (c : SkewSemistandardYoungTableau k) (i : Fin (k + 1)) :
    (c i).size ≤ c.outerShape.size :=
  c.size_mono (Fin.le_last i)

/-- Each step introduces at most one additional part. -/
theorem parts_card_le (c : SkewSemistandardYoungTableau k) (i : Fin (k + 1)) :
    (c i).parts.card ≤ c.innerShape.parts.card + i.val := by
  refine Fin.induction (by simp [innerShape]) (fun j hj => ?_) i
  have h := (c.interlaces j).card_le_succ
  simpa only [Fin.val_succ, Fin.val_castSucc, Nat.add_assoc] using
    h.trans (Nat.add_le_add_right hj 1)

/-- Natural subtraction in the weight loses no information. -/
theorem size_add_weight (c : SkewSemistandardYoungTableau k) (i : Fin k) :
    (c i.castSucc).size + c.weight i = (c i.succ).size :=
  Nat.add_sub_of_le (c.interlaces i).size_le

@[simp]
theorem weight_eq_zero_iff (c : SkewSemistandardYoungTableau k) (i : Fin k) :
    c.weight i = 0 ↔ c i.castSucc = c i.succ := by
  rw [(c.interlaces i).eq_iff_size_eq]
  have h := c.size_add_weight i
  omega

/-- The increments telescope to the difference between endpoint sizes. -/
theorem innerShape_size_add_sum_weight (c : SkewSemistandardYoungTableau k) :
    c.innerShape.size + ∑ i, c.weight i = c.outerShape.size := by
  have hsteps : (∑ i : Fin k, (c i.castSucc).size) + ∑ i, c.weight i =
      ∑ i : Fin k, (c i.succ).size := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => c.size_add_weight i
  have hinnerShape := Fin.sum_univ_succ (fun i => (c i).size)
  have houterShape := Fin.sum_univ_castSucc (fun i => (c i).size)
  dsimp [innerShape, outerShape]
  omega

theorem sum_weight (c : SkewSemistandardYoungTableau k) :
    ∑ i, c.weight i = c.outerShape.size - c.innerShape.size := by
  have h := c.innerShape_size_add_sum_weight
  omega

/-- The constant chain, including the chain with no steps when `k = 0`. -/
def const (k : ℕ) (μ : IntegerPartition) : SkewSemistandardYoungTableau k where
  toFun _ := μ
  interlaces _ := Interlaces.refl μ

@[simp]
theorem const_apply (μ : IntegerPartition) (i : Fin (k + 1)) : const k μ i = μ := rfl

@[simp]
theorem innerShape_const (μ : IntegerPartition) : (const k μ).innerShape = μ := rfl

@[simp]
theorem outerShape_const (μ : IntegerPartition) : (const k μ).outerShape = μ := rfl

@[simp]
theorem weight_const (μ : IntegerPartition) : (const k μ).weight = 0 := by
  funext i
  exact Nat.sub_self _

/-- A zero weight forces the entire chain to be constant. -/
theorem eq_const_of_weight_eq_zero (c : SkewSemistandardYoungTableau k) (h : c.weight = 0) :
    c = const k c.innerShape := by
  apply SkewSemistandardYoungTableau.ext
  intro i
  refine Fin.induction rfl (fun j hj => ?_) i
  have heq := (c.weight_eq_zero_iff j).mp (congrFun h j)
  exact heq.symm.trans hj

/-- The tableau obtained by adding one whole part at each step. After `k` steps its
shape is `μ.take k`; once all parts have been added, further steps have zero weight. -/
def rowTableau (μ : IntegerPartition) (k : ℕ) : SkewSemistandardYoungTableau k where
  toFun i := μ.take i.val
  interlaces i := μ.take_interlaces_take_succ i.val

@[simp]
theorem rowTableau_apply (μ : IntegerPartition) (i : Fin (k + 1)) :
    rowTableau μ k i = μ.take i.val := rfl

@[simp]
theorem innerShape_rowTableau (μ : IntegerPartition) :
    (rowTableau μ k).innerShape = empty :=
  μ.take_zero

@[simp]
theorem outerShape_rowTableau (μ : IntegerPartition) :
    (rowTableau μ k).outerShape = μ.take k := rfl

@[simp]
theorem weight_rowTableau (μ : IntegerPartition) (i : Fin k) :
    (rowTableau μ k).weight i = μ.part i := by
  simp [weight, IntegerPartition.size_take, Finset.sum_range_succ]

/-- Retain the first `l` steps. -/
def take (c : SkewSemistandardYoungTableau k) (l : ℕ) (h : l ≤ k) :
    SkewSemistandardYoungTableau l where
  toFun i := c (i.castLE (Nat.succ_le_succ h))
  interlaces i := c.interlaces (i.castLE h)

@[simp]
theorem take_apply (c : SkewSemistandardYoungTableau k) (l : ℕ) (h : l ≤ k) (i : Fin (l + 1)) :
    c.take l h i = c (i.castLE (Nat.succ_le_succ h)) := rfl

@[simp]
theorem innerShape_take (c : SkewSemistandardYoungTableau k) (l : ℕ) (h : l ≤ k) :
    (c.take l h).innerShape = c.innerShape := rfl

@[simp]
theorem outerShape_take (c : SkewSemistandardYoungTableau k) (l : ℕ) (h : l ≤ k) :
    (c.take l h).outerShape = c ⟨l, Nat.lt_succ_of_le h⟩ := rfl

@[simp]
theorem weight_take (c : SkewSemistandardYoungTableau k) (l : ℕ) (h : l ≤ k) (i : Fin l) :
    (c.take l h).weight i = c.weight (i.castLE h) := rfl

/-- The size of each term is the inner shape's size plus the corresponding prefix weight. -/
theorem size_eq_innerShape_add_sum_weight (c : SkewSemistandardYoungTableau k) (i : Fin (k + 1)) :
    (c i).size = c.innerShape.size +
      ∑ j : Fin i.val, c.weight (j.castLE (Nat.le_of_lt_succ i.isLt)) :=
  (c.take i.val (Nat.le_of_lt_succ i.isLt)).innerShape_size_add_sum_weight.symm

/-- Remove the final partition from a chain with at least one step. -/
def init (c : SkewSemistandardYoungTableau (k + 1)) : SkewSemistandardYoungTableau k where
  toFun i := c i.castSucc
  interlaces i := by
    simpa only [Fin.castSucc_succ] using c.interlaces i.castSucc

@[simp]
theorem init_apply (c : SkewSemistandardYoungTableau (k + 1)) (i : Fin (k + 1)) :
    c.init i = c i.castSucc := rfl

@[simp]
theorem innerShape_init (c : SkewSemistandardYoungTableau (k + 1)) :
    c.init.innerShape = c.innerShape := rfl

@[simp]
theorem weight_init (c : SkewSemistandardYoungTableau (k + 1)) (i : Fin k) :
    c.init.weight i = c.weight i.castSucc := by
  simp [weight]

/-- Append a partition that interlaces the last term. -/
def snoc (c : SkewSemistandardYoungTableau k) (ν : IntegerPartition)
    (h : c.outerShape.Interlaces ν) :
    SkewSemistandardYoungTableau (k + 1) where
  toFun := Fin.lastCases ν c
  interlaces i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [outerShape] using h
    · simpa only [← Fin.castSucc_succ, Fin.lastCases_castSucc] using c.interlaces j

@[simp]
theorem snoc_castSucc (c : SkewSemistandardYoungTableau k) (ν : IntegerPartition)
    (h : c.outerShape.Interlaces ν) (i : Fin (k + 1)) :
    c.snoc ν h i.castSucc = c i := by
  simp [snoc]

@[simp]
theorem outerShape_snoc (c : SkewSemistandardYoungTableau k) (ν : IntegerPartition)
    (h : c.outerShape.Interlaces ν) : (c.snoc ν h).outerShape = ν := by
  simp [outerShape, snoc]

@[simp]
theorem innerShape_snoc (c : SkewSemistandardYoungTableau k) (ν : IntegerPartition)
    (h : c.outerShape.Interlaces ν) : (c.snoc ν h).innerShape = c.innerShape := by
  exact snoc_castSucc c ν h 0

@[simp]
theorem weight_snoc_castSucc (c : SkewSemistandardYoungTableau k) (ν : IntegerPartition)
    (h : c.outerShape.Interlaces ν) (i : Fin k) :
    (c.snoc ν h).weight i.castSucc = c.weight i := by
  simp [weight, ← Fin.castSucc_succ]

@[simp]
theorem weight_snoc_last (c : SkewSemistandardYoungTableau k) (ν : IntegerPartition)
    (h : c.outerShape.Interlaces ν) :
    (c.snoc ν h).weight (Fin.last k) = ν.size - c.outerShape.size := by
  simp [weight, outerShape, snoc]

@[simp]
theorem init_snoc (c : SkewSemistandardYoungTableau k) (ν : IntegerPartition)
    (h : c.outerShape.Interlaces ν) : (c.snoc ν h).init = c := by
  apply SkewSemistandardYoungTableau.ext
  intro i
  simp

theorem init_outerShape_interlaces (c : SkewSemistandardYoungTableau (k + 1)) :
    c.init.outerShape.Interlaces c.outerShape := by
  simpa [outerShape] using c.interlaces (Fin.last k)

@[simp]
theorem snoc_init (c : SkewSemistandardYoungTableau (k + 1)) :
    c.init.snoc c.outerShape c.init_outerShape_interlaces = c := by
  apply SkewSemistandardYoungTableau.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact outerShape_snoc _ _ _
  · simp

/-- Tableaux of skew shape `ν / μ` and weight `w`. Taking `μ = empty` gives
ordinary semistandard tableaux of shape `ν`. -/
abbrev WithWeight (μ ν : IntegerPartition) (w : Fin k → ℕ) :=
  {c : SkewSemistandardYoungTableau k // c.innerShape = μ ∧ c.outerShape = ν ∧ c.weight = w}

namespace WithWeight

variable {μ ν : IntegerPartition} {w : Fin k → ℕ}

@[simp]
theorem innerShape_eq (c : WithWeight μ ν w) : c.val.innerShape = μ := c.property.1

@[simp]
theorem outerShape_eq (c : WithWeight μ ν w) : c.val.outerShape = ν := c.property.2.1

@[simp]
theorem weight_eq (c : WithWeight μ ν w) : c.val.weight = w := c.property.2.2

theorem size_add_weight (c : WithWeight μ ν w) (i : Fin k) :
    (c.val i.castSucc).size + w i = (c.val i.succ).size := by
  simpa using c.val.size_add_weight i

theorem size_eq (c : WithWeight μ ν w) : μ.size + ∑ i, w i = ν.size := by
  simpa using c.val.innerShape_size_add_sum_weight

theorem size_eq_sum_weight (c : WithWeight empty ν w) : ν.size = ∑ i, w i := by
  simpa using c.size_eq.symm

theorem size_eq_prefix_sum (c : WithWeight μ ν w) (i : Fin (k + 1)) :
    (c.val i).size = μ.size + ∑ j : Fin i.val, w (j.castLE (Nat.le_of_lt_succ i.isLt)) := by
  simpa using c.val.size_eq_innerShape_add_sum_weight i

/-- After `i` labels, an ordinary tableau has at most `i` parts, all bounded by
the corresponding parts of its final shape. -/
theorem part_le_take (c : WithWeight empty ν w) (i : Fin (k + 1)) (j : ℕ) :
    (c.val i).part j ≤ (ν.take i.val).part j := by
  have hc : (c.val i).parts.card ≤ i.val := by simpa using c.val.parts_card_le i
  rw [IntegerPartition.part_take]
  split_ifs with hj
  · have h : (c.val i).part j ≤ c.val.outerShape.part j :=
      c.val.part_mono j (Fin.le_last i)
    simpa only [c.outerShape_eq] using h
  · rw [IntegerPartition.part_eq_zero_of_card_le _ (by omega)]

/-- The only tableau whose weight is its shape's decreasing list of parts is
the tableau of successive prefixes. -/
theorem eq_rowTableau (c : WithWeight empty ν (fun i : Fin k => ν.part i)) :
    c.val = SkewSemistandardYoungTableau.rowTableau ν k := by
  apply SkewSemistandardYoungTableau.ext
  intro i
  apply IntegerPartition.eq_of_part_le_of_size_eq (c.part_le_take i)
  rw [c.size_eq_prefix_sum, IntegerPartition.size_take]
  simp only [IntegerPartition.size_empty, zero_add, Fin.val_castLE]
  rw [Fin.sum_univ_eq_sum_range]

instance : Subsingleton (WithWeight empty ν (fun i : Fin k => ν.part i)) where
  allEq c d := Subtype.ext (c.eq_rowTableau.trans d.eq_rowTableau.symm)

/-- The tableau of successive prefixes realizes the partition's own weight. -/
def rowTableau (ν : IntegerPartition) (hk : ν.parts.card ≤ k) :
    WithWeight empty ν (fun i : Fin k => ν.part i) :=
  ⟨SkewSemistandardYoungTableau.rowTableau ν k,
    by simp [ν.take_eq_self hk, funext (weight_rowTableau ν)]⟩

/-- All terms have bounded size, so there are finitely many such chains. -/
instance : Finite (WithWeight μ ν w) := by
  let f : WithWeight μ ν w → Fin (k + 1) → {π : IntegerPartition // π.size ≤ ν.size} :=
    fun c i => ⟨c.val i, by simpa using c.val.size_le_outerShape i⟩
  apply Finite.of_injective f
  intro c d h
  apply Subtype.ext
  apply SkewSemistandardYoungTableau.ext
  intro i
  exact congrArg Subtype.val (congrFun h i)

/-- An incompatible total weight gives no chains. -/
theorem isEmpty_of_size_ne (h : μ.size + ∑ i, w i ≠ ν.size) :
    IsEmpty (WithWeight μ ν w) :=
  ⟨fun c => h c.size_eq⟩

/-- The constant chain realizes the zero weight between equal endpoints. -/
def const (k : ℕ) (μ : IntegerPartition) : WithWeight μ μ (0 : Fin k → ℕ) :=
  ⟨SkewSemistandardYoungTableau.const k μ, by simp⟩

instance : Subsingleton (WithWeight μ ν (0 : Fin k → ℕ)) where
  allEq c d := by
    apply Subtype.ext
    have hc := c.val.eq_const_of_weight_eq_zero c.weight_eq
    have hd := d.val.eq_const_of_weight_eq_zero d.weight_eq
    rw [c.innerShape_eq] at hc
    rw [d.innerShape_eq] at hd
    exact hc.trans hd.symm

theorem init_outerShape_of_last_zero
    (T : WithWeight μ ν (Fin.lastCases 0 w)) : T.val.init.outerShape = ν := by
  have h := (T.val.weight_eq_zero_iff (Fin.last k)).mp (by rw [T.weight_eq]; simp)
  simpa only [outerShape, init_apply, Fin.succ_last] using h.trans T.outerShape_eq

/-- Adding an unused final label is an equivalence of tableaux with fixed weight. -/
def appendZeroEquiv (μ ν : IntegerPartition) (w : Fin k → ℕ) :
    WithWeight μ ν w ≃ WithWeight μ ν (Fin.lastCases 0 w) where
  toFun T := ⟨T.val.snoc ν (by rw [T.outerShape_eq]), by
    refine ⟨by simp, by simp, ?_⟩
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp⟩
  invFun T := ⟨T.val.init, by
    refine ⟨by simp, T.init_outerShape_of_last_zero, ?_⟩
    funext i
    simp [T.weight_eq]⟩
  left_inv T := by
    apply Subtype.ext
    apply SkewSemistandardYoungTableau.ext
    intro i
    simp
  right_inv T := by
    apply Subtype.ext
    apply SkewSemistandardYoungTableau.ext
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [snoc, outerShape, Fin.lastCases_last] using T.outerShape_eq.symm
    · simp

end WithWeight

end SkewSemistandardYoungTableau

