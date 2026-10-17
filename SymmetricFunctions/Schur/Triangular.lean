import SymmetricFunctions.Schur.JacobiTrudi
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The integral triangular transition from Schur to complete functions

The sum of squared parts is only an ordering statistic. Symmetric-function
degree remains the sum of the parts. A nonidentity determinant term strictly
increases this statistic; negative determinant indices make the term zero.
-/

noncomputable section
open scoped BigOperators

namespace SymmetricFunctions.Partition

variable {d : ℕ}

/-- An ordering statistic for the transition matrix, not symmetric-function degree. -/
def squareWeight (ξ : Nat.Partition d) : ℕ := (ξ.parts.map (fun n => n ^ 2)).sum

/-- The positive rows recover the parts, in their decreasing order. -/
theorem parts_eq_rows (ξ : Nat.Partition d) :
    ξ.parts = (List.ofFn (fun i : Fin (length ξ) => rowLength ξ i) : Multiset ℕ) := by
  calc
    ξ.parts = (ξ.parts.sort (· ≥ ·) : Multiset ℕ) := (Multiset.sort_eq _ _).symm
    _ = _ := by
      apply congrArg (fun l : List ℕ => (l : Multiset ℕ))
      apply List.ext_getElem
      · simp [length]
      · intro i hi hi'
        simp only [List.getElem_ofFn]
        exact (rowLength_eq_getElem_sort ξ i (by simpa [length] using hi)).symm

/-- The ordering statistic can equally be read from all the positive rows. -/
theorem squareWeight_eq_sum_rows (ξ : Nat.Partition d) :
    squareWeight ξ = ∑ i : Fin (length ξ), rowLength ξ i ^ 2 := by
  rw [squareWeight, parts_eq_rows]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_ofFn, List.sum_ofFn, Function.comp_def]

end SymmetricFunctions.Partition

namespace SymmetricFunction

open SymmetricFunctions.Partition
variable {d L : ℕ}

/-- The integer index occurring in a determinant permutation term. -/
def jacobiTrudiIndex (ξ : Nat.Partition d) (σ : Equiv.Perm (Fin L)) (i : Fin L) : ℤ :=
  (rowLength ξ (σ i) : ℤ) - (σ i : ℤ) + (i : ℤ)

/-- Row reordering cancels the index shifts in the total degree. -/
theorem sum_jacobiTrudiIndex (ξ : Nat.Partition d) (σ : Equiv.Perm (Fin L))
    (hL : length ξ ≤ L) : ∑ i, jacobiTrudiIndex ξ σ i = (d : ℤ) := by
  have hrows : ∑ i : Fin L, (rowLength ξ i : ℤ) = (d : ℤ) := by
    exact_mod_cast (Fin.sum_univ_eq_sum_range (rowLength ξ) L).trans
      (sum_rowLength_padded ξ hL)
  simp only [jacobiTrudiIndex, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Equiv.sum_comp σ (fun i : Fin L => (rowLength ξ i : ℤ)),
    Equiv.sum_comp σ (fun i : Fin L => (i : ℤ)), hrows]
  ring

/-- A nonidentity permutation strictly increases the sum of squared indices.
This is an integer inequality and does not assume the indices are nonnegative. -/
theorem sum_sq_jacobiTrudiIndex_gt (ξ : Nat.Partition d)
    (σ : Equiv.Perm (Fin L)) (hσ : σ ≠ 1) :
    (∑ i : Fin L, (rowLength ξ i : ℤ) ^ 2) < ∑ i, jacobiTrudiIndex ξ σ i ^ 2 := by
  have ha : Antivary (fun i : Fin L => (rowLength ξ i : ℤ)) (fun i => (i : ℤ)) := by
    intro i j hij
    dsimp only at hij ⊢
    exact_mod_cast rowLength_antitone ξ (show i.val ≤ j.val by omega)
  have hr := ha.sum_mul_le_sum_comp_perm_mul (σ := σ)
  have hp : 0 < ∑ i : Fin L, ((i : ℤ) - (σ i : ℤ)) ^ 2 := by
    apply Finset.sum_pos'
    · intro i _
      positivity
    · have hex : ∃ i, σ i ≠ i := by
        by_contra! h
        exact hσ (Equiv.ext h)
      obtain ⟨i, hi⟩ := hex
      refine ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero ?_⟩
      intro h
      apply hi
      apply Fin.ext
      omega
  have he : ∑ i, jacobiTrudiIndex ξ σ i ^ 2 =
      (∑ i : Fin L, (rowLength ξ i : ℤ) ^ 2) +
      (∑ i : Fin L, ((i : ℤ) - (σ i : ℤ)) ^ 2) +
      2 * ((∑ i : Fin L, (rowLength ξ (σ i) : ℤ) * (i : ℤ)) -
        ∑ i : Fin L, (rowLength ξ i : ℤ) * (i : ℤ)) := by
    calc
      _ = ∑ i : Fin L, ((rowLength ξ (σ i) : ℤ) ^ 2 +
          ((i : ℤ) - (σ i : ℤ)) ^ 2 +
          2 * ((rowLength ξ (σ i) : ℤ) * (i : ℤ) -
            (rowLength ξ (σ i) : ℤ) * (σ i : ℤ))) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [jacobiTrudiIndex]
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_sub_distrib,
          Equiv.sum_comp σ (fun i : Fin L => (rowLength ξ i : ℤ) ^ 2),
          Equiv.sum_comp σ (fun i : Fin L => (rowLength ξ i : ℤ) * (i : ℤ))]
  omega


variable {R : Type*} [CommRing R]

/-- The complete partition product is the product over positive rows. -/
theorem hPart_eq_prod_rows (ξ : Nat.Partition d) :
    hPart (R := R) ξ = ∏ i : Fin (length ξ), h (rowLength ξ i) := by
  rw [hPart, parts_eq_rows]
  simp only [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, List.prod_ofFn, Function.comp_def]

private theorem prod_map_filter_ne_zero {A : Type*} [CommMonoid A]
    (s : Multiset ℕ) (f : ℕ → A) (h0 : f 0 = 1) :
    ((s.filter (· ≠ 0)).map f).prod = (s.map f).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    by_cases ha : a = 0
    · subst a
      simp [Multiset.filter_cons_of_neg, h0, ih]
    · simp [ha, ih]

/-- Removing zero indices does not change a complete product. -/
theorem hPart_ofSums (a : Multiset ℕ) (ha : a.sum = d) :
    hPart (R := R) (Nat.Partition.ofSums d a ha) = (a.map h).prod := by
  exact prod_map_filter_ne_zero a h h_zero

private theorem sum_sq_filter_ne_zero (s : Multiset ℕ) :
    ((s.filter (· ≠ 0)).map (fun n => n ^ 2)).sum = (s.map (fun n => n ^ 2)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    by_cases ha : a = 0
    · subst a
      simp [Multiset.filter_cons_of_neg, ih]
    · simp [ha, ih]

/-- Removing zero indices leaves the square statistic unchanged. -/
theorem squareWeight_ofSums (a : Multiset ℕ) (ha : a.sum = d) :
    squareWeight (Nat.Partition.ofSums d a ha) = (a.map (fun n => n ^ 2)).sum :=
  sum_sq_filter_ne_zero a

/-- Partition of a nonvanishing determinant term, removing its zero indices. -/
def jacobiTrudiPartition (ξ : Nat.Partition d) (σ : Equiv.Perm (Fin (length ξ)))
    (ha : ∀ i, 0 ≤ jacobiTrudiIndex ξ σ i) : Nat.Partition d :=
  Nat.Partition.ofSums d
    (List.ofFn (fun i => (jacobiTrudiIndex ξ σ i).toNat)) (by
      rw [Multiset.sum_coe, List.sum_ofFn]
      apply Int.natCast_inj.mp
      simpa only [Nat.cast_sum, Int.toNat_of_nonneg (ha _)] using
        sum_jacobiTrudiIndex ξ σ le_rfl)

/-- Identity permutation yields the original partition, including the empty shape. -/
@[simp] theorem jacobiTrudiPartition_one (ξ : Nat.Partition d)
    (ha : ∀ i, 0 ≤ jacobiTrudiIndex ξ 1 i) : jacobiTrudiPartition ξ 1 ha = ξ := by
  apply Nat.Partition.ext
  change (Multiset.filter (· ≠ 0)
    (List.ofFn (fun i : Fin (length ξ) => (jacobiTrudiIndex ξ 1 i).toNat))) = ξ.parts
  simp only [jacobiTrudiIndex, Equiv.Perm.one_apply, sub_add_cancel, Int.toNat_natCast]
  rw [← parts_eq_rows, Multiset.filter_eq_self]
  intro a ha
  exact (ξ.parts_pos ha).ne'

/-- The square statistic of each surviving off-diagonal term strictly increases. -/
theorem squareWeight_jacobiTrudiPartition_gt (ξ : Nat.Partition d)
    (σ : Equiv.Perm (Fin (length ξ))) (ha : ∀ i, 0 ≤ jacobiTrudiIndex ξ σ i)
    (hσ : σ ≠ 1) : squareWeight ξ < squareWeight (jacobiTrudiPartition ξ σ ha) := by
  rw [jacobiTrudiPartition, squareWeight_ofSums, squareWeight_eq_sum_rows]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_ofFn, List.sum_ofFn,
    Function.comp_def]
  apply Int.ofNat_lt.mp
  simpa only [Nat.cast_sum, Nat.cast_pow, Int.toNat_of_nonneg (ha _)] using
    sum_sq_jacobiTrudiIndex_gt ξ σ hσ

/-- Unsigned product belonging to one determinant permutation. -/
def jacobiTrudiTerm (ξ : Nat.Partition d) (σ : Equiv.Perm (Fin (length ξ))) :
    SymmetricFunction R := ∏ i, jacobiTrudiMatrix ξ (length ξ) (σ i) i

theorem jacobiTrudiTerm_eq_zero (ξ : Nat.Partition d)
    (σ : Equiv.Perm (Fin (length ξ))) (ha : ¬ ∀ i, 0 ≤ jacobiTrudiIndex ξ σ i) :
    jacobiTrudiTerm (R := R) ξ σ = 0 := by
  obtain ⟨i, hi⟩ := not_forall.mp ha
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact completeInt_of_neg (lt_of_not_ge hi)

theorem jacobiTrudiTerm_eq_hPart (ξ : Nat.Partition d)
    (σ : Equiv.Perm (Fin (length ξ))) (ha : ∀ i, 0 ≤ jacobiTrudiIndex ξ σ i) :
    jacobiTrudiTerm (R := R) ξ σ = hPart (jacobiTrudiPartition ξ σ ha) := by
  rw [jacobiTrudiPartition, hPart_ofSums]
  simp only [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, List.prod_ofFn,
    Function.comp_def]
  apply Finset.prod_congr rfl
  intro i _
  change completeInt (jacobiTrudiIndex ξ σ i) = h _
  simp only [completeInt, ha i, ite_true]

@[simp] theorem jacobiTrudiTerm_one (ξ : Nat.Partition d) :
    jacobiTrudiTerm (R := R) ξ 1 = hPart ξ := by
  rw [jacobiTrudiTerm_eq_hPart ξ 1 (by intro i; simp [jacobiTrudiIndex]),
    jacobiTrudiPartition_one]

/-- The determinant expansion with scalar signs in the coefficient ring. -/
theorem schur_eq_sum_jacobiTrudiTerm (ξ : Nat.Partition d) :
    schur (R := R) ξ = ∑ σ, (Equiv.Perm.sign σ : ℤ) • jacobiTrudiTerm ξ σ := by
  rw [schur, Matrix.det_apply]
  rfl

/-- Complete-basis coordinates of the actual Jacobi–Trudi determinants. -/
def schurCompleteTransition (R : Type*) [CommRing R] (d : ℕ) :
    Matrix (Nat.Partition d) (Nat.Partition d) R :=
  fun μ ξ => (hBasisAll R).repr (schur ξ) ⟨d, μ⟩

/-- These are also the coordinates in the homogeneous complete basis. -/
theorem schurCompleteTransition_eq_repr (μ ξ : Nat.Partition d) :
    schurCompleteTransition R d μ ξ =
      (hBasis R d).repr ⟨schur ξ, isHomogeneous_schur ξ⟩ μ := by
  rw [schurCompleteTransition, hBasisAll_repr, hBasis_repr]

private theorem hBasisAll_repr_hPart (μ ξ : Nat.Partition d) :
    (hBasisAll R).repr (hPart ξ) ⟨d, μ⟩ = if μ = ξ then 1 else 0 := by
  rw [← hBasisAll_apply (R := R) ⟨d, ξ⟩, Module.Basis.repr_self]
  simp [Finsupp.single_apply, eq_comm]

/-- Identity diagonal blocks and strict triangularity with respect to squareWeight.
No division, domain hypothesis, or nontriviality assumption occurs. -/
theorem schurCompleteTransition_eq_delta_of_le (μ ξ : Nat.Partition d)
    (hμ : squareWeight μ ≤ squareWeight ξ) :
    schurCompleteTransition R d μ ξ = if μ = ξ then 1 else 0 := by
  classical
  rw [schurCompleteTransition, schur_eq_sum_jacobiTrudiTerm, map_sum,
    Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single 1]
  · simp only [Equiv.Perm.sign_one, Units.val_one, one_zsmul, jacobiTrudiTerm_one]
    exact hBasisAll_repr_hPart μ ξ
  · intro σ _ hσ
    by_cases ha : ∀ i, 0 ≤ jacobiTrudiIndex ξ σ i
    · rw [jacobiTrudiTerm_eq_hPart ξ σ ha, map_zsmul]
      have hne : μ ≠ jacobiTrudiPartition ξ σ ha := by
        intro he
        have := squareWeight_jacobiTrudiPartition_gt ξ σ ha hσ
        rw [← he] at this
        omega
      simp [Finsupp.smul_apply, hBasisAll_repr_hPart, hne]
    · rw [jacobiTrudiTerm_eq_zero ξ σ ha]
      simp
  · simp

@[simp] theorem schurCompleteTransition_diagonal (ξ : Nat.Partition d) :
    schurCompleteTransition R d ξ ξ = 1 := by
  rw [schurCompleteTransition_eq_delta_of_le ξ ξ le_rfl, ite_eq_left rfl]

/-- The transition determinant is one over every commutative coefficient ring. -/
theorem det_schurCompleteTransition (R : Type*) [CommRing R] (d : ℕ) :
    (schurCompleteTransition R d).det = 1 := by
  classical
  have ht : (schurCompleteTransition R d).transpose.BlockTriangular squareWeight := by
    intro i j hij
    change schurCompleteTransition R d j i = 0
    rw [schurCompleteTransition_eq_delta_of_le j i hij.le]
    exact ite_eq_right (fun h => (ne_of_lt hij) (congrArg squareWeight h))
  rw [← Matrix.det_transpose, ht.det]
  apply Finset.prod_eq_one
  intro k _
  have hb : (schurCompleteTransition R d).transpose.toSquareBlock squareWeight k = 1 := by
    ext i j
    change schurCompleteTransition R d j.val i.val = _
    rw [schurCompleteTransition_eq_delta_of_le j.val i.val
      (by rw [i.property, j.property])]
    simp [Matrix.one_apply, Subtype.ext_iff, eq_comm]
  rw [hb, Matrix.det_one]

end SymmetricFunction
