import SymmetricFunctions.Tableaux.Basic
import SymmetricFunctions.Partition.Orbits

/-!
# Partition content and natural Kostka counts

Partition content lists decreasing row lengths: entry i occurs μ_i times.
A Kostka number counts this one specified content, not its permutation orbit.
-/

noncomputable section
open scoped BigOperators

namespace SymmetricFunctions.Partition

variable {d N : ℕ} {ξ : Nat.Partition d}

/-- Decreasing partition content in a finite alphabet, padded with zeros. -/
def rowContent (μ : Nat.Partition d) (N : ℕ) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => rowLength μ i.val)

@[simp] theorem rowContent_apply (μ : Nat.Partition d) (i : Fin N) :
    rowContent μ N i = rowLength μ i.val := rfl

/-- Padding partition content adds only zero coordinates. -/
theorem rowContent_embDomain (μ : Nat.Partition d) {M : ℕ}
    (hM : length μ ≤ M) (hMN : M ≤ N) :
    (rowContent μ M).embDomain (Fin.castLEEmb hMN) = rowContent μ N := by
  ext i
  by_cases hi : i.val < M
  · exact Finsupp.embDomain_apply_self (Fin.castLEEmb hMN) (rowContent μ M) ⟨i, hi⟩
  · rw [Finsupp.embDomain_of_notMem_range]
    · exact (rowLength_eq_zero μ (by omega)).symm
    · rintro ⟨j, hj⟩
      have := congrArg Fin.val hj
      simp at this
      omega

/-- The nonzero exponent multiset of partition content is the partition itself. -/
theorem exponentParts_rowContent (μ : Nat.Partition d) (hN : length μ ≤ N) :
    exponentParts (rowContent μ N) = μ.parts := by
  classical
  rw [← rowContent_embDomain μ le_rfl hN, exponentParts_embDomain]
  have hs : (rowContent μ (length μ)).support = Finset.univ := by
    ext i
    simp only [Finsupp.mem_support_iff, rowContent_apply, Finset.mem_univ, iff_true]
    exact Nat.ne_of_gt ((rowLength_pos_iff μ i).mpr i.isLt)
  rw [exponentParts, hs, Fin.univ_val_map]
  have hl : List.ofFn (fun i : Fin (length μ) => rowContent μ (length μ) i) =
      μ.parts.sort (· ≥ ·) := by
    apply List.ext_getElem
    · simp [length]
    · intro i hi hj
      simp only [List.getElem_ofFn, rowContent_apply]
      exact rowLength_eq_getElem_sort μ i (by simpa using hi)
  simp [hl]

/-- Every sufficient partition content has total degree equal to its size. -/
theorem degree_rowContent (μ : Nat.Partition d) (hN : length μ ≤ N) :
    (rowContent μ N).degree = d := by
  simpa only [Finsupp.degree_apply, Finsupp.sum] using
    (sum_exponentParts (rowContent μ N)).symm.trans
      ((congrArg Multiset.sum (exponentParts_rowContent μ hN)).trans μ.parts_sum)

/-- Prefix content is the same explicit prefix of decreasing row lengths. -/
theorem weight_rowContent_prefix (μ : Nat.Partition d) (hN : length μ ≤ N) (k : ℕ) :
    Finsupp.weight (fun i : Fin N => if i.val < k then 1 else 0) (rowContent μ N) =
      ∑ i ∈ Finset.range k, rowLength μ i := by
  classical
  rw [Finsupp.weight_eq_sum]
  simp only [rowContent_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < k then rowLength μ i else 0),
    ← Finset.sum_filter]
  apply Finset.sum_subset
  · intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  · intro i hi hn
    have hk : i < k := Finset.mem_range.mp hi
    have hNi : N ≤ i := by
      simpa only [Finset.mem_filter, Finset.mem_range, hk, and_true, not_lt] using hn
    exact rowLength_eq_zero μ (hN.trans hNi)

namespace FiniteTableau

/-- The canonical row filling has precisely the partition's decreasing content. -/
@[simp] theorem content_highestWeight (ξ : Nat.Partition d) (hN : length ξ ≤ N) :
    content (highestWeight ξ hN) = rowContent ξ N := by
  classical
  ext k
  rw [content_apply, rowContent_apply, rowLength, YoungDiagram.rowLen_eq_card]
  have he : (Finset.univ.filter fun c => filling (highestWeight ξ hN) c = k) =
      (YoungDiagram.ofPartition ξ).cells.attach.filter (fun c => c.val.1 = k.val) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_attach, true_and]
    rw [Fin.ext_iff]
    change ((highestWeight ξ hN).val c.val.1 c.val.2 = k.val) ↔ _
    rw [highestWeight_entry hN c.property]
  rw [he, Finset.filter_attach (fun c : ℕ × ℕ => c.1 = k.val),
    Finset.card_map, Finset.card_attach]
  rfl

/-- Summing a statistic of the entries is the corresponding content weight. -/
theorem weight_content (T : FiniteTableau ξ N) (w : Fin N → ℕ) :
    Finsupp.weight w (content T) = ∑ c, w (filling T c) := by
  simp only [content, map_sum, Finsupp.weight_single, one_smul]

/-- Equality with the row content forces every cell to carry its row number. -/
theorem eq_highestWeight_of_content (ξ : Nat.Partition d) (hN : length ξ ≤ N)
    (T : FiniteTableau ξ N) (hT : content T = rowContent ξ N) :
    T = highestWeight ξ hN := by
  classical
  have hs : (∑ c, (filling (highestWeight ξ hN) c).val) =
      ∑ c, (filling T c).val := by
    rw [← weight_content, ← weight_content, content_highestWeight, hT]
  have hle (c : {c // c ∈ (YoungDiagram.ofPartition ξ).cells}) :
      (filling (highestWeight ξ hN) c).val ≤ (filling T c).val := by
    change (highestWeight ξ hN).val c.val.1 c.val.2 ≤ T.val c.val.1 c.val.2
    rw [highestWeight_entry hN c.property]
    exact row_le_entry T c.property
  have he := (Finset.sum_eq_sum_iff_of_le (fun c _ => hle c)).mp hs
  apply filling_injective
  funext c
  exact Fin.ext (he c (Finset.mem_univ c)).symm

/-- The decreasing content of the shape admits just its canonical row filling. -/
@[simp] theorem contentCount_diagonal (ξ : Nat.Partition d) (hN : length ξ ≤ N) :
    contentCount ξ (rowContent ξ N) = 1 := by
  classical
  let : Unique {T : FiniteTableau ξ N // content T = rowContent ξ N} :=
    { default := ⟨highestWeight ξ hN, content_highestWeight ξ hN⟩
      uniq T := Subtype.ext (eq_highestWeight_of_content ξ hN T.val T.property) }
  exact Fintype.card_unique

end FiniteTableau

/-- Natural Kostka number: tableaux of shape ξ and the single content μ. -/
def kostka (ξ μ : Nat.Partition d) : ℕ :=
  FiniteTableau.contentCount ξ (rowContent μ d)

@[simp] theorem kostka_self (ξ : Nat.Partition d) : kostka ξ ξ = 1 :=
  FiniteTableau.contentCount_diagonal ξ (parts_card_le ξ)

/-- Dominance direction: the Schur shape has larger prefix row sums than the content. -/
def Dominates (ξ μ : Nat.Partition d) : Prop :=
  ∀ k, (∑ i ∈ Finset.range k, rowLength μ i) ≤ ∑ i ∈ Finset.range k, rowLength ξ i

/-- Every semistandard tableau has shape dominating its partition content.
Letters below k can occur only in the first k rows, by strict columns. -/
theorem FiniteTableau.dominates_of_content (ξ μ : Nat.Partition d)
    (T : FiniteTableau ξ N) (hμ : length μ ≤ N) (hT : T.content = rowContent μ N) :
    Dominates ξ μ := by
  classical
  intro k
  rw [← weight_rowContent_prefix μ hμ k,
    ← weight_rowContent_prefix ξ T.length_le k, ← hT,
    ← FiniteTableau.content_highestWeight ξ T.length_le,
    FiniteTableau.weight_content, FiniteTableau.weight_content]
  apply Finset.sum_le_sum
  intro c _
  have hle := FiniteTableau.row_le_entry T c.property
  have he : (FiniteTableau.filling (FiniteTableau.highestWeight ξ T.length_le) c).val =
      c.val.1 := FiniteTableau.highestWeight_entry T.length_le c.property
  rw [he]
  change (if T.val c.val.1 c.val.2 < k then 1 else 0) ≤ _
  by_cases ht : T.val c.val.1 c.val.2 < k
  · have hc : c.val.1 < k := lt_of_le_of_lt hle ht
    simp only [ht, hc, ite_true, le_refl]
  · simp only [ht, ite_false]
    exact Nat.zero_le _

/-- Failure of the displayed prefix-sum dominance inequalities forces zero. -/
theorem kostka_eq_zero_of_not_dominates (ξ μ : Nat.Partition d)
    (h : ¬ Dominates ξ μ) : kostka ξ μ = 0 := by
  classical
  let : IsEmpty {T : FiniteTableau ξ d // T.content = rowContent μ d} :=
    ⟨fun T => h (T.val.dominates_of_content ξ μ (parts_card_le μ) T.property)⟩
  exact Fintype.card_eq_zero

end SymmetricFunctions.Partition
