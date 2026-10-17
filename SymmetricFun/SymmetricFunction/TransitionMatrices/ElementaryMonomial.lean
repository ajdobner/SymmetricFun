module

public import SymmetricFun.Matrix.Partition
public import SymmetricFun.SymmetricFunction.Elementary
public import SymmetricFun.SymmetricFunction.Monomial

/-!
# Elementary coefficients as counts of binary matrices

For arbitrary finite families `a : I → ℕ` and `b : J → ℕ`, the coefficient of
`∏ j, X (v j) ^ b j` in `∏ i, esymm σ R (a i)` counts binary matrices with row
sums `a` and column sums `b`. Here `v : J ↪ σ` chooses distinct variables.
No positivity, sortedness, or equality of the two total sums is assumed.

The partition specialization allows any enumeration of the parts. In particular,
the counting formula is independent of the order in which those parts are listed.
`msymmPart_basis_repr_esymmPartGraded_eq_card` expresses the corresponding entry
of the elementary-to-monomial transition matrix.

The matrix count vanishes unless the conjugate of the elementary index dominates
the monomial index, and is one when the two are equal. Thus, indexing elementary
products by conjugate partitions gives a unitriangular transition matrix.
-/

@[expose] public section
noncomputable section

namespace MvPowerSeries

variable {I J σ : Type*} [Fintype I] [Fintype J]
variable (R : Type*) [CommSemiring R]

private theorem degree_eq_sum (d : J →₀ ℕ) :
    d.degree = ∑ j, d j :=
  Finsupp.sum_fintype d (fun _ n => n) (fun _ => rfl)

/-- In finitely many variables, an elementary product coefficient counts binary matrices. -/
theorem coeff_prod_esymm_finite (a : I → ℕ) (b : J → ℕ) :
    coeff (Finsupp.equivFunOnFinite.symm b) (∏ i, esymm J R (a i)) =
      (Nat.card (Matrix.BinaryWithMargins a b) : R) := by
  classical
  let s := (Finset.finsuppAntidiag Finset.univ
    (Finsupp.equivFunOnFinite.symm b)).filter
      (fun l : I →₀ (J →₀ ℕ) => ∀ i, (l i).degree = a i ∧ ∀ j, l i j ≤ 1)
  let e : {l // l ∈ s} ≃ Matrix.BinaryWithMargins a b := {
    toFun := fun l => ⟨Matrix.of (fun i j => l.val i j), by
      refine ⟨?_, fun i j => ((Finset.mem_filter.mp l.property).2 i).2 j⟩
      constructor
      · intro i
        exact (degree_eq_sum (l.val i)).symm.trans ((Finset.mem_filter.mp l.property).2 i).1
      · intro j
        have h := (Finset.mem_finsuppAntidiag.mp
          (Finset.mem_filter.mp l.property).1).1
        simpa using congrArg (fun d : J →₀ ℕ => d j) h⟩
    invFun := fun B =>
      ⟨Finsupp.equivFunOnFinite.symm (fun i =>
        Finsupp.equivFunOnFinite.symm (fun j => B.val i j)), by
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_finsuppAntidiag.mpr
          refine ⟨?_, Finset.subset_univ _⟩
          ext j
          simp
        · intro i
          constructor
          · rw [degree_eq_sum]
            exact B.row_sum i
          · intro j
            exact B.entry_le_one i j⟩
    left_inv := fun l => by
      apply Subtype.ext
      ext i j
      rfl
    right_inv := fun B => by
      apply Subtype.ext
      ext i j
      rfl }
  calc
    _ = ∑ l ∈ Finset.finsuppAntidiag Finset.univ (Finsupp.equivFunOnFinite.symm b),
        if (∀ i, (l i).degree = a i ∧ ∀ j, l i j ≤ 1) then (1 : R) else 0 := by
      rw [coeff_prod]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [coeff_esymm_eq_ite]
      exact Fintype.prod_boole (M₀ := R)
        (p := fun i => (l i).degree = a i ∧ ∀ j, l i j ≤ 1)
    _ = (s.card : R) := Finset.sum_boole _ _
    _ = _ := by
      congr 1
      rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

/-- The same coefficient count in any ambient variable type, along an embedding. -/
theorem coeff_prod_esymm_embDomain (a : I → ℕ) (b : J → ℕ) (v : J ↪ σ) :
    coeff ((Finsupp.equivFunOnFinite.symm b).embDomain v) (∏ i, esymm σ R (a i)) =
      (Nat.card (Matrix.BinaryWithMargins a b) : R) := by
  rw [← coeff_killCompl]
  simp only [map_prod, killCompl_esymm]
  exact coeff_prod_esymm_finite R a b

/-- The coefficient of a monomial in distinct variables in an elementary product is
the number of binary matrices with the specified row and column sums. -/
theorem coeff_prod_esymm (a : I → ℕ) (b : J → ℕ) (v : J ↪ σ) :
    coeff (∑ j, Finsupp.single (v j) (b j)) (∏ i, esymm σ R (a i)) =
      (Nat.card (Matrix.BinaryWithMargins a b) : R) := by
  simpa only [Finsupp.equivFunOnFinite_symm_eq_sum, Finsupp.embDomain_eq_mapDomain,
    Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single] using
      coeff_prod_esymm_embDomain R a b v

/-- The coefficient formula for an elementary partition product, using any finite
enumeration of its parts. -/
theorem coeff_esymmPart_eq_card {n : ℕ} (α : Nat.Partition n) (a : I → ℕ)
    (ha : Finset.univ.val.map a = α.parts) (b : J → ℕ) (v : J ↪ σ) :
    coeff (∑ j, Finsupp.single (v j) (b j)) (esymmPart σ R α) =
      (Nat.card (Matrix.BinaryWithMargins a b) : R) := by
  rw [esymmPart_eq_prod σ R α a ha]
  exact coeff_prod_esymm R a b v

/-- The monomial coordinate of an elementary partition product counts binary matrices.
Both partitions may be enumerated in any order, with repeated parts kept as separate indices. -/
theorem msymmPart_basis_repr_esymmPartGraded_eq_card [Infinite σ] {n : ℕ}
    (α β : Nat.Partition n) (a : I → ℕ) (b : J → ℕ)
    (ha : Finset.univ.val.map a = α.parts) (hb : Finset.univ.val.map b = β.parts)
    (v : J ↪ σ) :
    (msymmPart_basis σ R n).repr (esymmPartGraded σ R α) β =
      (Nat.card (Matrix.BinaryWithMargins a b) : R) := by
  classical
  let d : J →₀ ℕ := Finsupp.equivFunOnFinite.symm b
  have hpos (j : J) : 0 < b j := by
    apply β.parts_pos
    rw [← hb]
    exact Multiset.mem_map.mpr ⟨j, by simp, rfl⟩
  have hs : d.support = Finset.univ := by
    ext j
    simp [d, (hpos j).ne']
  have hd : (d.embDomain v).toAllPartitions = β.toAllPartitions := by
    rw [Finsupp.embDomain_toAllPartitions]
    apply AllPartitions.ext
    change d.support.val.map d = β.parts
    rw [hs]
    exact hb
  rw [msymmPart_basis_repr_apply_eq_coeff σ R
    (esymmPartGraded σ R α) β (d.embDomain v) hd]
  change coeff (d.embDomain v) (esymmPart σ R α) = _
  rw [esymmPart_eq_prod σ R α a ha]
  exact coeff_prod_esymm_embDomain R a b v

/-- The monomial coordinate counts matrices with the canonical decreasing part labels. -/
theorem msymmPart_basis_repr_esymmPartGraded_eq_card_partition [Infinite σ] {n : ℕ}
    (α β : Nat.Partition n) :
    (msymmPart_basis σ R n).repr (esymmPartGraded σ R α) β =
      (Nat.card (Matrix.BinaryWithPartitionMargins α β) : R) := by
  exact msymmPart_basis_repr_esymmPartGraded_eq_card R α β
    (fun i : Fin ((YoungDiagram.ofPartition α).colLen 0) =>
      (YoungDiagram.ofPartition α).rowLen i)
    (fun j : Fin ((YoungDiagram.ofPartition β).colLen 0) =>
      (YoungDiagram.ofPartition β).rowLen j)
    α.map_rowLen β.map_rowLen (Fin.valEmbedding.trans (Infinite.natEmbedding σ))

/-- An elementary product has no monomial term outside the conjugate dominance bound. -/
theorem msymmPart_basis_repr_esymmPartGraded_eq_zero [Infinite σ] {n : ℕ}
    (α β : Nat.Partition n) (h : ¬ α.conjugate.Dominates β) :
    (msymmPart_basis σ R n).repr (esymmPartGraded σ R α) β = 0 := by
  let : IsEmpty (Matrix.BinaryWithPartitionMargins α β) :=
    ⟨fun B => h (Matrix.BinaryWithPartitionMargins.conjugate_dominates B)⟩
  rw [msymmPart_basis_repr_esymmPartGraded_eq_card_partition]
  simp

/-- The leading monomial coefficient of an elementary product is one. -/
@[simp]
theorem msymmPart_basis_repr_esymmPartGraded_conjugate [Infinite σ] {n : ℕ}
    (α : Nat.Partition n) :
    (msymmPart_basis σ R n).repr (esymmPartGraded σ R α) α.conjugate = 1 := by
  rw [msymmPart_basis_repr_esymmPartGraded_eq_card_partition,
    Matrix.BinaryWithPartitionMargins.card_conjugate, Nat.cast_one]

end MvPowerSeries
