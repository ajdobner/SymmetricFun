import SymmetricFunctions.Partition.YoungDiagram

/-! # Horizontal strips of the existing Mathlib Young diagrams -/
namespace SymmetricFunctions.Partition
variable {d e : ℕ} {ξ : Nat.Partition d} {μ : Nat.Partition e}

/-- A horizontal strip is contained and has interlacing row lengths. -/
def HorizontalStrip (μ : Nat.Partition e) (ξ : Nat.Partition d) : Prop :=
  Contained μ ξ ∧ ∀ i, rowLength ξ (i + 1) ≤ rowLength μ i

/-- An interlacing difference has at most one cell in each column. -/
theorem HorizontalStrip.eq_row_of_cells (h : HorizontalStrip μ ξ) {i k j : ℕ}
    (hi : (i, j) ∈ YoungDiagram.ofPartition ξ)
    (hi' : (i, j) ∉ YoungDiagram.ofPartition μ)
    (hk : (k, j) ∈ YoungDiagram.ofPartition ξ)
    (hk' : (k, j) ∉ YoungDiagram.ofPartition μ) : i = k := by
  have no_lt {a b : ℕ} (ha : (a, j) ∉ YoungDiagram.ofPartition μ)
      (hb : (b, j) ∈ YoungDiagram.ofPartition ξ) : ¬ a < b := by
    intro hab
    have hm : rowLength μ a ≤ j := Nat.le_of_not_gt (fun hj =>
      ha (YoungDiagram.mem_iff_lt_rowLen.mpr hj))
    have hx : j < rowLength ξ b := YoungDiagram.mem_iff_lt_rowLen.mp hb
    have hb' := rowLength_antitone ξ (Nat.succ_le_of_lt hab)
    change rowLength ξ b ≤ rowLength ξ (a + 1) at hb'
    have hh := h.2 a
    omega
  exact le_antisymm (Nat.le_of_not_gt (no_lt hk' hi)) (Nat.le_of_not_gt (no_lt hi' hk))

/-- The cell condition implies the row-interlacing condition, without any new shape type. -/
theorem horizontalStrip_of_column_injective (hc : Contained μ ξ)
    (h : ∀ i k j, (i, j) ∈ YoungDiagram.ofPartition ξ →
      (i, j) ∉ YoungDiagram.ofPartition μ → (k, j) ∈ YoungDiagram.ofPartition ξ →
      (k, j) ∉ YoungDiagram.ofPartition μ → i = k) : HorizontalStrip μ ξ := by
  refine ⟨hc, fun i => ?_⟩
  by_contra hh
  have hi : rowLength μ i < rowLength ξ (i + 1) := Nat.lt_of_not_ge hh
  have hrow := rowLength_antitone ξ (Nat.le_succ i)
  have hμ := rowLength_antitone μ (Nat.le_succ i)
  have h0 : (i, rowLength μ i) ∈ YoungDiagram.ofPartition ξ :=
    YoungDiagram.mem_iff_lt_rowLen.mpr (lt_of_lt_of_le hi hrow)
  have h1 : (i + 1, rowLength μ i) ∈ YoungDiagram.ofPartition ξ :=
    YoungDiagram.mem_iff_lt_rowLen.mpr hi
  have h0' : (i, rowLength μ i) ∉ YoungDiagram.ofPartition μ := by
    rw [YoungDiagram.mem_iff_lt_rowLen]
    exact lt_irrefl _
  have h1' : (i + 1, rowLength μ i) ∉ YoungDiagram.ofPartition μ := by
    rw [YoungDiagram.mem_iff_lt_rowLen]
    exact Nat.not_lt_of_ge hμ
  have := h i (i + 1) (rowLength μ i) h0 h0' h1 h1'
  omega

@[simp] theorem horizontalStrip_self (ξ : Nat.Partition d) : HorizontalStrip ξ ξ :=
  ⟨le_rfl, fun i => rowLength_antitone ξ (Nat.le_succ i)⟩

end SymmetricFunctions.Partition
