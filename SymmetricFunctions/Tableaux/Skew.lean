import SymmetricFunctions.Tableaux.Basic
import SymmetricFunctions.Partition.HorizontalStrip

/-!
# Finite skew tableaux on existing Young diagrams

Containment is a proof field. Entries and comparisons use only cells of the
actual difference; no outside values or extension to a straight tableau occur.
-/
noncomputable section
open scoped BigOperators

namespace SymmetricFunctions.Partition

variable {d e N : ℕ}

/-- Actual cells in a difference of Mathlib Young diagrams. A skew tableau also
requires containment; an arbitrary difference alone is not a skew shape. -/
abbrev SkewCell (ξ : Nat.Partition d) (μ : Nat.Partition e) :=
  {c // c ∈ (YoungDiagram.ofPartition ξ).cells \ (YoungDiagram.ofPartition μ).cells}

/-- A finite skew filling. Both cells in every comparison are present. -/
structure SkewTableau (ξ : Nat.Partition d) (μ : Nat.Partition e) (N : ℕ) where
  contained : Contained μ ξ
  entry : SkewCell ξ μ → Fin N
  row_weak : ∀ c c', c.val.1 = c'.val.1 → c.val.2 ≤ c'.val.2 → entry c ≤ entry c'
  col_strict : ∀ c c', c.val.2 = c'.val.2 → c.val.1 < c'.val.1 → entry c < entry c'

namespace SkewTableau
variable {ξ : Nat.Partition d} {μ : Nat.Partition e}

@[ext] theorem ext {T U : SkewTableau ξ μ N} (h : ∀ c, T.entry c = U.entry c) : T = U := by
  cases T
  cases U
  congr
  exact funext h

theorem entry_injective : Function.Injective (entry (ξ := ξ) (μ := μ) (N := N)) :=
  fun _ _ h => ext (congrFun h)

instance : Fintype (SkewTableau ξ μ N) := Fintype.ofInjective entry entry_injective

/-- Count letters only in actual skew cells. -/
def content (T : SkewTableau ξ μ N) : Fin N →₀ ℕ :=
  ∑ c, Finsupp.single (T.entry c) 1

theorem content_apply (T : SkewTableau ξ μ N) (k : Fin N) :
    content T k = (Finset.univ.filter fun c => T.entry c = k).card := by
  classical
  simp [content, Finsupp.single_apply]

@[simp] theorem degree_content (T : SkewTableau ξ μ N) : (content T).degree = d - e := by
  classical
  simp only [content, map_sum, Finsupp.degree_single, Finset.sum_const, smul_eq_mul,
    mul_one, Finset.card_univ, Fintype.card_coe]
  rw [Finset.card_sdiff_of_subset (YoungDiagram.cells_subset_iff.mpr T.contained)]
  simp only [YoungDiagram.card_ofPartition]

def weight (R : Type*) [CommSemiring R] (T : SkewTableau ξ μ N) : MvPolynomial (Fin N) R :=
  MvPolynomial.monomial (content T) 1

theorem weight_eq_prod (R : Type*) [CommSemiring R] (T : SkewTableau ξ μ N) :
    weight R T = ∏ c, MvPolynomial.X (T.entry c) := by
  classical
  simp only [weight, content, MvPolynomial.monomial_sum_one, MvPolynomial.X]

def generatingPolynomial (ξ : Nat.Partition d) (μ : Nat.Partition e) (N : ℕ)
    (R : Type*) [CommSemiring R] : MvPolynomial (Fin N) R :=
  ∑ T : SkewTableau ξ μ N, weight R T

def contentCount (ξ : Nat.Partition d) (μ : Nat.Partition e) (a : Fin N →₀ ℕ) : ℕ :=
  Fintype.card {T : SkewTableau ξ μ N // content T = a}

theorem coeff_generatingPolynomial (R : Type*) [CommSemiring R] (ξ : Nat.Partition d)
    (μ : Nat.Partition e) (a : Fin N →₀ ℕ) :
    (generatingPolynomial ξ μ N R).coeff a = (contentCount ξ μ a : R) := by
  classical
  simp [generatingPolynomial, weight, MvPolynomial.coeff_monomial, contentCount,
    Fintype.card_subtype, eq_comm]

@[simp] theorem map_weight {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (T : SkewTableau ξ μ N) : MvPolynomial.map f (weight R T) = weight S T := by
  simp [weight]

@[simp] theorem map_generatingPolynomial {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (ξ : Nat.Partition d) (μ : Nat.Partition e) (N : ℕ) :
    MvPolynomial.map f (generatingPolynomial ξ μ N R) = generatingPolynomial ξ μ N S := by
  simp [generatingPolynomial]

theorem isEmpty_of_not_contained (h : ¬ Contained μ ξ) : IsEmpty (SkewTableau ξ μ N) :=
  ⟨fun T => h T.contained⟩

theorem generatingPolynomial_eq_zero_of_not_contained (R : Type*) [CommSemiring R]
    (h : ¬ Contained μ ξ) : generatingPolynomial ξ μ N R = 0 := by
  let := isEmpty_of_not_contained (N := N) h
  simp [generatingPolynomial]

instance (ξ : Nat.Partition d) (N : ℕ) : Unique (SkewTableau ξ ξ N) where
  default :=
    { contained := le_rfl
      entry := fun c => False.elim (by simpa using c.property)
      row_weak := fun c => False.elim (by simpa using c.property)
      col_strict := fun c => False.elim (by simpa using c.property) }
  uniq T := ext (fun c => False.elim (by simpa using c.property))

@[simp] theorem content_self (ξ : Nat.Partition d) (T : SkewTableau ξ ξ N) : content T = 0 :=
  (Finsupp.degree_eq_zero_iff _).mp (by simp)

@[simp] theorem weight_self (R : Type*) [CommSemiring R] (ξ : Nat.Partition d)
    (T : SkewTableau ξ ξ N) : weight R T = 1 := by simp [weight]

@[simp] theorem generatingPolynomial_self (ξ : Nat.Partition d) (N : ℕ)
    (R : Type*) [CommSemiring R] : generatingPolynomial ξ ξ N R = 1 := by
  simp [generatingPolynomial]

private theorem not_mem_empty (μ : Nat.Partition 0) (c : ℕ × ℕ) :
    c ∉ YoungDiagram.ofPartition μ := by
  rw [YoungDiagram.mem_iff_lt_rowLen]
  change ¬ c.2 < rowLength μ c.1
  simp

/-- With empty inner shape, the actual cell sets agree. -/
def emptyCellEquiv (ξ : Nat.Partition d) (μ : Nat.Partition 0) :
    SkewCell ξ μ ≃ {c // c ∈ (YoungDiagram.ofPartition ξ).cells} where
  toFun c := ⟨c.val, (Finset.mem_sdiff.mp c.property).1⟩
  invFun c := ⟨c.val, Finset.mem_sdiff.mpr ⟨c.property, not_mem_empty μ c.val⟩⟩

/-- The straight Mathlib filling, viewed as a skew filling with empty inner shape. -/
def ofStraight (μ : Nat.Partition 0) (T : FiniteTableau ξ N) : SkewTableau ξ μ N where
  contained := zero_contained μ ξ
  entry c := T.filling (emptyCellEquiv ξ μ c)
  row_weak c c' hi hj := by
    change T.val c.val.1 c.val.2 ≤ T.val c'.val.1 c'.val.2
    rw [hi]
    exact T.val.row_weak_of_le hj (emptyCellEquiv ξ μ c').property
  col_strict c c' hj hi := by
    change T.val c.val.1 c.val.2 < T.val c'.val.1 c'.val.2
    rw [hj]
    exact T.val.col_strict hi (emptyCellEquiv ξ μ c').property

/-- Recover the genuine Mathlib straight tableau, using its required outside zeros. -/
def toStraight {μ : Nat.Partition 0} (T : SkewTableau ξ μ N) : FiniteTableau ξ N := by
  classical
  let f : ℕ → ℕ → ℕ := fun i j =>
    if hc : (i, j) ∈ YoungDiagram.ofPartition ξ then
      (T.entry ((emptyCellEquiv ξ μ).symm ⟨(i, j), hc⟩)).val else 0
  refine ⟨⟨f, ?_, ?_, ?_⟩, ?_⟩
  · intro i j k hj hk
    have hc := (YoungDiagram.ofPartition ξ).up_left_mem le_rfl hj.le hk
    dsimp [f]
    rw [dite_eq_left hk, dite_eq_left hc]
    exact T.row_weak _ _ rfl hj.le
  · intro i k j hi hk
    have hc := (YoungDiagram.ofPartition ξ).up_left_mem hi.le le_rfl hk
    dsimp [f]
    rw [dite_eq_left hk, dite_eq_left hc]
    exact T.col_strict _ _ rfl hi
  · intro i j hc
    exact dite_eq_right hc
  · intro i j hc
    change f i j < N
    dsimp [f]
    rw [dite_eq_left hc]
    exact (T.entry _).isLt

@[simp] theorem toStraight_ofStraight (μ : Nat.Partition 0) (T : FiniteTableau ξ N) :
    toStraight (ofStraight μ T) = T := by
  classical
  apply Subtype.ext
  apply SemistandardYoungTableau.ext
  intro i j
  change (if hc : (i, j) ∈ YoungDiagram.ofPartition ξ then
    ((ofStraight μ T).entry ((emptyCellEquiv ξ μ).symm ⟨(i, j), hc⟩)).val else 0) = T.val i j
  by_cases hc : (i, j) ∈ YoungDiagram.ofPartition ξ
  · rw [dite_eq_left hc]
    rfl
  · rw [dite_eq_right hc, T.val.zeros hc]

@[simp] theorem ofStraight_toStraight {μ : Nat.Partition 0} (T : SkewTableau ξ μ N) :
    ofStraight μ (toStraight T) = T := by
  classical
  apply ext
  intro c
  apply Fin.ext
  change (if hc : (c.val.1, c.val.2) ∈ YoungDiagram.ofPartition ξ then
    (T.entry ((emptyCellEquiv ξ μ).symm ⟨(c.val.1, c.val.2), hc⟩)).val else 0) = _
  have hc : (c.val.1, c.val.2) ∈ YoungDiagram.ofPartition ξ :=
    (Finset.mem_sdiff.mp c.property).1
  rw [dite_eq_left hc]
  rfl

/-- An actual content-preserving equivalence with Mathlib's straight tableaux. -/
def straightEquiv (ξ : Nat.Partition d) (μ : Nat.Partition 0) (N : ℕ) :
    FiniteTableau ξ N ≃ SkewTableau ξ μ N where
  toFun := ofStraight μ
  invFun := toStraight
  left_inv := toStraight_ofStraight μ
  right_inv := ofStraight_toStraight

@[simp] theorem content_ofStraight (μ : Nat.Partition 0) (T : FiniteTableau ξ N) :
    content (ofStraight μ T) = FiniteTableau.content T := by
  classical
  exact (emptyCellEquiv ξ μ).sum_comp (fun c => Finsupp.single (T.filling c) 1)

@[simp] theorem weight_ofStraight (R : Type*) [CommSemiring R] (μ : Nat.Partition 0)
    (T : FiniteTableau ξ N) : weight R (ofStraight μ T) = FiniteTableau.weight R T := by
  simp [weight, FiniteTableau.weight]

@[simp] theorem generatingPolynomial_empty (ξ : Nat.Partition d) (μ : Nat.Partition 0)
    (N : ℕ) (R : Type*) [CommSemiring R] :
    generatingPolynomial ξ μ N R = FiniteTableau.generatingPolynomial ξ N R := by
  classical
  rw [generatingPolynomial, ← (straightEquiv ξ μ N).sum_comp (weight R)]
  simp only [straightEquiv, Equiv.coe_fn_mk, weight_ofStraight,
    FiniteTableau.generatingPolynomial]

theorem isEmpty_zero_alphabet (hd : e < d) : IsEmpty (SkewTableau ξ μ 0) := by
  refine ⟨fun T => ?_⟩
  have he : content T = 0 := Subsingleton.elim _ _
  have hh := degree_content T
  rw [he, map_zero] at hh
  omega

theorem generatingPolynomial_zero_alphabet (R : Type*) [CommSemiring R] (hd : e < d) :
    generatingPolynomial ξ μ 0 R = 0 := by
  let := isEmpty_zero_alphabet (ξ := ξ) (μ := μ) hd
  simp [generatingPolynomial]

/-- One-letter fillings cannot distinguish two cells in a column. -/
theorem horizontalStrip_of_one (T : SkewTableau ξ μ 1) : HorizontalStrip μ ξ := by
  apply horizontalStrip_of_column_injective T.contained
  intro i k j hi hi' hk hk'
  let c : SkewCell ξ μ := ⟨(i, j), Finset.mem_sdiff.mpr ⟨hi, hi'⟩⟩
  let c' : SkewCell ξ μ := ⟨(k, j), Finset.mem_sdiff.mpr ⟨hk, hk'⟩⟩
  have he : T.entry c = T.entry c' := Subsingleton.elim _ _
  rcases lt_trichotomy i k with hik | hik | hik
  · have hh := T.col_strict c c' rfl hik
    exact False.elim ((ne_of_lt hh) he)
  · exact hik
  · have hh := T.col_strict c' c rfl hik
    exact False.elim ((ne_of_lt hh) he.symm)

/-- A horizontal strip can be filled with any one letter. Missing inner cells
impose no comparisons. -/
def constant (h : HorizontalStrip μ ξ) (k : Fin N) : SkewTableau ξ μ N where
  contained := h.1
  entry _ := k
  row_weak _ _ _ _ := le_rfl
  col_strict c c' hj hi := by
    have hc := Finset.mem_sdiff.mp c.property
    have hc' := Finset.mem_sdiff.mp c'.property
    have hc1 : (c'.val.1, c.val.2) ∈ YoungDiagram.ofPartition ξ := by
      rw [hj]
      exact hc'.1
    have hc2 : (c'.val.1, c.val.2) ∉ YoungDiagram.ofPartition μ := by
      rw [hj]
      exact hc'.2
    have he := h.eq_row_of_cells hc.1 hc.2 hc1 hc2
    exact False.elim ((ne_of_lt hi) he)

instance : Subsingleton (SkewTableau ξ μ 1) := ⟨fun _ _ => ext (fun _ => Subsingleton.elim _ _)⟩

theorem nonempty_one_iff : Nonempty (SkewTableau ξ μ 1) ↔ HorizontalStrip μ ξ :=
  ⟨fun ⟨T⟩ => horizontalStrip_of_one T, fun h => ⟨constant h 0⟩⟩

theorem content_one (T : SkewTableau ξ μ 1) : content T = Finsupp.single 0 (d - e) := by
  have hh : content T = Finsupp.single 0 (content T 0) := by
    apply Finsupp.ext
    intro k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    simp
  have hd := degree_content T
  rw [hh, Finsupp.degree_single] at hd
  rwa [hd] at hh

theorem generatingPolynomial_one_of_horizontalStrip (R : Type*) [CommSemiring R]
    (h : HorizontalStrip μ ξ) :
    generatingPolynomial ξ μ 1 R = MvPolynomial.X (0 : Fin 1) ^ (d - e) := by
  let : Unique (SkewTableau ξ μ 1) :=
    { default := constant h 0, uniq := fun _ => Subsingleton.elim _ _ }
  simp only [generatingPolynomial, Finset.univ_unique, Finset.sum_singleton, weight,
    content_one, MvPolynomial.X_pow_eq_monomial]

open Classical in
/-- The genuine one-letter skew weight sum, including noncontained shapes. -/
theorem generatingPolynomial_one (R : Type*) [CommSemiring R] :
    generatingPolynomial ξ μ 1 R =
      if HorizontalStrip μ ξ then MvPolynomial.X (0 : Fin 1) ^ (d - e) else 0 := by
  classical
  by_cases h : HorizontalStrip μ ξ
  · simpa [h] using generatingPolynomial_one_of_horizontalStrip R h
  · let : IsEmpty (SkewTableau ξ μ 1) := ⟨fun T => h (horizontalStrip_of_one T)⟩
    simp [generatingPolynomial, h]

end SkewTableau
end SymmetricFunctions.Partition
