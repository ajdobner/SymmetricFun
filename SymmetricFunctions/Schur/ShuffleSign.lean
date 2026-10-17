import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.BigOperators.Fin

/-! # Signs of two increasing blocks

Only pairs crossing the blocks can be inversions. The result takes values in
integer units and can be mapped into any coefficient ring.
-/

namespace SymmetricFunctions

open scoped BigOperators

/-- The sign of a shuffle is the product of its cross-block comparison signs. -/
theorem sign_orderedShuffle {l w : ℕ} (e : Fin l ⊕ Fin w ≃ Fin (l + w))
    (hl : StrictMono (fun i => e (Sum.inl i)))
    (hr : StrictMono (fun j => e (Sum.inr j))) :
    Equiv.Perm.sign (finSumFinEquiv.symm.trans e) =
      ∏ i : Fin l, ∏ j : Fin w, (if e (Sum.inl i) < e (Sum.inr j) then 1 else -1 : ℤˣ) := by
  classical
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
  have hprod (i : Fin (l + w)) :
      (∏ j ∈ Finset.Ioi i,
        (if (finSumFinEquiv.symm.trans e) i < (finSumFinEquiv.symm.trans e) j
          then 1 else -1 : ℤˣ)) =
      ∏ j : Fin (l + w), (if i < j then
        (if e (finSumFinEquiv.symm i) < e (finSumFinEquiv.symm j) then 1 else -1) else 1 : ℤˣ) := by
    rw [← Finset.prod_filter]
    apply Finset.prod_congr
    · ext j
      simp
    · intro j _
      rfl
  simp_rw [hprod]
  rw [← finSumFinEquiv.prod_comp]
  simp_rw [← finSumFinEquiv.prod_comp]
  simp only [Fintype.prod_sum_type, Equiv.symm_apply_apply, finSumFinEquiv_apply_left,
    finSumFinEquiv_apply_right,
    hl.lt_iff_lt, hr.lt_iff_lt]
  have hcross (i : Fin l) (j : Fin w) : Fin.castAdd w i < Fin.natAdd l j := by
    change i.val < l + j.val
    omega
  have hleft (i j : Fin l) : Fin.castAdd w i < Fin.castAdd w j ↔ i < j := Iff.rfl
  have hright (i j : Fin w) : Fin.natAdd l i < Fin.natAdd l j ↔ i < j := by
    change l + i.val < l + j.val ↔ i.val < j.val
    omega
  have hdiag (p : Prop) [Decidable p] :
      (if p then (if p then 1 else -1) else 1 : ℤˣ) = 1 := by
    split_ifs <;> rfl
  simp [hcross, (hcross _ _).not_gt, hleft, hright, hdiag]

/-- Compare two block enumerations using their signs in the same finite order. -/
theorem sign_relativeShuffle {l w : ℕ} (e f : Fin l ⊕ Fin w ≃ Fin (l + w)) :
    Equiv.Perm.sign (e.trans f.symm) =
      Equiv.Perm.sign (finSumFinEquiv.symm.trans e) *
        Equiv.Perm.sign (finSumFinEquiv.symm.trans f) := by
  let c : Fin l ⊕ Fin w ≃ Fin (l + w) := finSumFinEquiv
  have he : (c.symm.trans (e.trans f.symm)).trans c =
      (c.symm.trans e).trans (c.symm.trans f).symm := by
    ext i
    simp
  rw [← Equiv.Perm.sign_symm_trans_trans (e.trans f.symm) c, he,
    Equiv.Perm.sign_trans, Equiv.Perm.sign_symm, mul_comm]

end SymmetricFunctions
