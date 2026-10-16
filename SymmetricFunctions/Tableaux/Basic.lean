import SymmetricFunctions.Partition.YoungDiagram
import Mathlib.Data.Finsupp.Weight
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Bounded Mathlib tableaux, content and weights

Entries are zero-based: entry `k : Fin N` labels the variable `X k`, called
x_(k+1) in the paper. Row zero is the longest row; French drawings put it at
the bottom. Content counts actual cells, never Mathlib's zeros outside shape.
-/

noncomputable section

open scoped BigOperators

namespace SymmetricFunctions.Partition

variable {d N : ℕ} {ξ : Nat.Partition d}

namespace FiniteTableau

/-- The actual filling of the finite Young diagram. -/
def filling (T : FiniteTableau ξ N)
    (c : {c // c ∈ (YoungDiagram.ofPartition ξ).cells}) : Fin N :=
  ⟨T.val c.val.1 c.val.2, T.property _ _ c.property⟩

theorem filling_injective : Function.Injective (filling (ξ := ξ) (N := N)) := by
  intro T U h
  apply Subtype.ext
  apply SemistandardYoungTableau.ext
  intro i j
  by_cases hc : (i, j) ∈ YoungDiagram.ofPartition ξ
  · exact congrArg Fin.val (congrFun h ⟨(i, j), hc⟩)
  · rw [T.val.zeros hc, U.val.zeros hc]

/-- Finiteness follows from the finite space of actual cell fillings. -/
instance : Fintype (FiniteTableau ξ N) :=
  Fintype.ofInjective filling filling_injective

/-- Content is the sum of one unit at the entry of each actual cell. -/
def content (T : FiniteTableau ξ N) : Fin N →₀ ℕ :=
  ∑ c, Finsupp.single (filling T c) 1

/-- Each entry multiplicity is a finite fiber cardinality. -/
theorem content_apply (T : FiniteTableau ξ N) (k : Fin N) :
    content T k = (Finset.univ.filter fun c => filling T c = k).card := by
  classical
  simp [content, Finsupp.single_apply]

/-- Every cell contributes exactly one letter. -/
@[simp] theorem degree_content (T : FiniteTableau ξ N) : (content T).degree = d := by
  classical
  simp only [content, map_sum, Finsupp.degree_single, Finset.sum_const, smul_eq_mul,
    mul_one, Finset.card_univ, Fintype.card_coe, YoungDiagram.card_ofPartition]

/-- A constant filling has all its cells in one content coordinate. -/
theorem content_eq_single_of_constant (T : FiniteTableau ξ N) (k : Fin N)
    (h : ∀ c, filling T c = k) : content T = Finsupp.single k d := by
  classical
  ext l
  by_cases hl : k = l
  · subst l
    simp [content_apply, h, YoungDiagram.card_ofPartition]
  · simp [content_apply, h, hl]

/-- The monomial carried by a tableau, with coefficient one. -/
def weight (R : Type*) [CommSemiring R] (T : FiniteTableau ξ N) : MvPolynomial (Fin N) R :=
  MvPolynomial.monomial (content T) 1

/-- Counting entries is equivalent to multiplying one variable per cell. -/
theorem weight_eq_prod (R : Type*) [CommSemiring R] (T : FiniteTableau ξ N) :
    weight R T = ∏ c, MvPolynomial.X (filling T c) := by
  classical
  simp only [weight, content, MvPolynomial.monomial_sum_one, MvPolynomial.X]

/-- Tableau weights have the number of cells as their total alphabet degree. -/
theorem isHomogeneous_weight (R : Type*) [CommSemiring R] (T : FiniteTableau ξ N) :
    MvPolynomial.IsHomogeneous (weight R T) d :=
  MvPolynomial.isHomogeneous_monomial 1 (degree_content T)

/-- The genuine finite weight sum. Its Schur identification is a separate theorem. -/
def generatingPolynomial (ξ : Nat.Partition d) (N : ℕ) (R : Type*) [CommSemiring R] :
    MvPolynomial (Fin N) R := ∑ T : FiniteTableau ξ N, weight R T

theorem isHomogeneous_generatingPolynomial (ξ : Nat.Partition d) (N : ℕ)
    (R : Type*) [CommSemiring R] :
    MvPolynomial.IsHomogeneous (generatingPolynomial ξ N R) d := by
  exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun T _ => isHomogeneous_weight R T)

/-- A coefficient-ring-independent number of tableaux of one specified content. -/
def contentCount (ξ : Nat.Partition d) (a : Fin N →₀ ℕ) : ℕ :=
  Fintype.card {T : FiniteTableau ξ N // content T = a}

@[simp] theorem map_weight {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (T : FiniteTableau ξ N) : MvPolynomial.map f (weight R T) = weight S T := by
  simp [weight]

@[simp] theorem map_generatingPolynomial {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (ξ : Nat.Partition d) (N : ℕ) :
    MvPolynomial.map f (generatingPolynomial ξ N R) = generatingPolynomial ξ N S := by
  simp [generatingPolynomial]

theorem coeff_generatingPolynomial (R : Type*) [CommSemiring R] (ξ : Nat.Partition d)
    (a : Fin N →₀ ℕ) :
    (generatingPolynomial ξ N R).coeff a = (contentCount ξ a : R) := by
  classical
  simp [generatingPolynomial, weight, MvPolynomial.coeff_monomial, contentCount,
    Fintype.card_subtype, eq_comm]

/-- Strict columns force the entry in row i to be at least i. -/
theorem row_le_entry (T : FiniteTableau ξ N) {i j : ℕ}
    (hc : (i, j) ∈ YoungDiagram.ofPartition ξ) : i ≤ T.val i j := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have hc' := (YoungDiagram.ofPartition ξ).up_left_mem (Nat.le_succ i) le_rfl hc
    exact Nat.succ_le_of_lt (lt_of_le_of_lt (ih hc') (T.val.col_strict (Nat.lt_succ_self i) hc))

/-- A bounded tableau has at most as many rows as alphabet letters. -/
theorem length_le (T : FiniteTableau ξ N) : length ξ ≤ N := by
  by_contra h
  have hc : (N, 0) ∈ YoungDiagram.ofPartition ξ :=
    YoungDiagram.mem_iff_lt_rowLen.mpr ((rowLength_pos_iff ξ N).mpr (by omega))
  exact (Nat.not_lt_of_ge (row_le_entry T hc)) (T.property N 0 hc)

theorem isEmpty_of_length_gt (h : N < length ξ) : IsEmpty (FiniteTableau ξ N) :=
  ⟨fun T => (Nat.not_le_of_gt h) (length_le T)⟩

theorem generatingPolynomial_eq_zero_of_length_gt (R : Type*) [CommSemiring R]
    (h : N < length ξ) : generatingPolynomial ξ N R = 0 := by
  let := isEmpty_of_length_gt h
  simp [generatingPolynomial]

/-- The canonical tableau: every cell in row i carries entry i. -/
def highestWeight (ξ : Nat.Partition d) (hN : length ξ ≤ N) : FiniteTableau ξ N :=
  ⟨SemistandardYoungTableau.highestWeight (YoungDiagram.ofPartition ξ), by
    intro i j hc
    rw [SemistandardYoungTableau.highestWeight_apply, ite_eq_left hc]
    have hi : i < length ξ := (rowLength_pos_iff ξ i).mp
      (lt_of_le_of_lt (Nat.zero_le j) (YoungDiagram.mem_iff_lt_rowLen.mp hc))
    omega⟩

@[simp] theorem highestWeight_entry (hN : length ξ ≤ N) {i j : ℕ}
    (hc : (i, j) ∈ YoungDiagram.ofPartition ξ) :
    (highestWeight ξ hN).val i j = i := by
  simp [highestWeight, hc]

/-- The row obstruction is exact, including the empty alphabet. -/
theorem nonempty_iff : Nonempty (FiniteTableau ξ N) ↔ length ξ ≤ N :=
  ⟨fun ⟨T⟩ => length_le T, fun h => ⟨highestWeight ξ h⟩⟩

instance (ξ : Nat.Partition 0) (N : ℕ) : Unique (FiniteTableau ξ N) where
  default := highestWeight ξ (by simp)
  uniq T := by
    apply Subtype.ext
    apply SemistandardYoungTableau.ext
    intro i j
    have hc : (i, j) ∉ YoungDiagram.ofPartition ξ := by
      rw [YoungDiagram.mem_iff_lt_rowLen]
      change ¬ j < rowLength ξ i
      simp
    rw [T.val.zeros hc, (highestWeight ξ (by simp)).val.zeros hc]

@[simp] theorem content_zero (ξ : Nat.Partition 0) (T : FiniteTableau ξ N) :
    content T = 0 := (Finsupp.degree_eq_zero_iff _).mp (degree_content T)

@[simp] theorem weight_zero (R : Type*) [CommSemiring R] (ξ : Nat.Partition 0)
    (T : FiniteTableau ξ N) : weight R T = 1 := by
  simp [weight]

@[simp] theorem generatingPolynomial_zero (ξ : Nat.Partition 0) (N : ℕ)
    (R : Type*) [CommSemiring R] : generatingPolynomial ξ N R = 1 := by
  simp [generatingPolynomial]

@[simp] theorem contentCount_zero (ξ : Nat.Partition 0) (a : Fin N →₀ ℕ) :
    contentCount ξ a = if a = 0 then 1 else 0 := by
  classical
  by_cases ha : a = 0 <;> simp [contentCount, Fintype.card_subtype, eq_comm, ha]

theorem isEmpty_zero_alphabet (hd : d ≠ 0) : IsEmpty (FiniteTableau ξ 0) := by
  refine ⟨fun T => hd ?_⟩
  have he : content T = 0 := Subsingleton.elim _ _
  simpa [he] using (degree_content T).symm

theorem generatingPolynomial_zero_alphabet (R : Type*) [CommSemiring R] (hd : d ≠ 0) :
    generatingPolynomial ξ 0 R = 0 := by
  let := isEmpty_zero_alphabet (ξ := ξ) hd
  simp [generatingPolynomial]

theorem contentCount_eq_zero_of_degree_ne (a : Fin N →₀ ℕ) (ha : a.degree ≠ d) :
    contentCount ξ a = 0 := by
  classical
  let : IsEmpty {T : FiniteTableau ξ N // content T = a} :=
    ⟨fun T => ha (T.property ▸ degree_content T.val)⟩
  exact Fintype.card_eq_zero

end FiniteTableau
end SymmetricFunctions.Partition
