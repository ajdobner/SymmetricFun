module

public import SymmetricFun.Tableau.Basic
public import SymmetricFun.Partition.BenderKnuth

/-!
# Bender–Knuth involutions on skew tableaux

`benderKnuth i` reflects the partition between labels `i.castSucc` and `i.succ`.
It preserves the skew shape, is an involution, and exchanges those two weight
entries. These involutions are sufficient to prove symmetry of tableau counts;
no braid relations or symmetric-group action on tableaux are asserted.
-/

@[expose] public section

open IntegerPartition

namespace SkewSemistandardYoungTableau

variable {k : ℕ}

/-- Exchange the multiplicities of two adjacent labels by reflecting their
intermediate partition. -/
def benderKnuth (i : Fin k) (T : SkewSemistandardYoungTableau (k + 1)) :
    SkewSemistandardYoungTableau (k + 1) where
  toFun := Function.update T i.castSucc.succ
    (benderKnuthMiddle (T i.castSucc.castSucc) (T i.castSucc.succ) (T i.succ.succ))
  interlaces j := by
    by_cases hl : j = i.castSucc
    · subst j
      rw [Function.update_self, Function.update_of_ne (by simp [Fin.ext_iff])]
      exact interlaces_benderKnuthMiddle (T.interlaces i.castSucc) (T.interlaces i.succ)
    · by_cases hr : j = i.succ
      · subst j
        simp only [Fin.castSucc_succ]
        rw [Function.update_self, Function.update_of_ne (by simp [Fin.ext_iff])]
        exact benderKnuthMiddle_interlaces (T.interlaces i.castSucc) (T.interlaces i.succ)
      · rw [Function.update_of_ne (by simp_all [Fin.ext_iff]),
          Function.update_of_ne (by simp_all [Fin.ext_iff])]
        exact T.interlaces j

@[simp]
theorem benderKnuth_apply_middle (i : Fin k) (T : SkewSemistandardYoungTableau (k + 1)) :
    benderKnuth i T i.castSucc.succ =
      benderKnuthMiddle (T i.castSucc.castSucc) (T i.castSucc.succ) (T i.succ.succ) := by
  simp [benderKnuth]

theorem benderKnuth_apply_of_ne (i : Fin k) (T : SkewSemistandardYoungTableau (k + 1))
    (j : Fin (k + 2)) (h : j ≠ i.castSucc.succ) :
    benderKnuth i T j = T j :=
  Function.update_of_ne h _ _

@[simp]
theorem innerShape_benderKnuth (i : Fin k) (T : SkewSemistandardYoungTableau (k + 1)) :
    (benderKnuth i T).innerShape = T.innerShape :=
  benderKnuth_apply_of_ne i T 0 (by simp_all [Fin.ext_iff])

@[simp]
theorem outerShape_benderKnuth (i : Fin k) (T : SkewSemistandardYoungTableau (k + 1)) :
    (benderKnuth i T).outerShape = T.outerShape :=
  benderKnuth_apply_of_ne i T (Fin.last (k + 1)) (by
    simp_all [Fin.ext_iff]
    omega)

theorem benderKnuth_involutive (i : Fin k) : Function.Involutive (benderKnuth i) := by
  intro T
  apply SkewSemistandardYoungTableau.ext
  intro j
  by_cases hj : j = i.castSucc.succ
  · subst j
    rw [benderKnuth_apply_middle, benderKnuth_apply_middle,
      benderKnuth_apply_of_ne _ _ _ (by simp_all [Fin.ext_iff]),
      benderKnuth_apply_of_ne _ _ _ (by simp_all [Fin.ext_iff])]
    exact benderKnuthMiddle_involutive (T.interlaces i.castSucc) (T.interlaces i.succ)
  · rw [benderKnuth_apply_of_ne _ _ _ hj, benderKnuth_apply_of_ne _ _ _ hj]

/-- Bender–Knuth as a self-equivalence of all tableaux on the given alphabet. -/
def benderKnuthEquiv (i : Fin k) :
    SkewSemistandardYoungTableau (k + 1) ≃ SkewSemistandardYoungTableau (k + 1) where
  toFun := benderKnuth i
  invFun := benderKnuth i
  left_inv := benderKnuth_involutive i
  right_inv := benderKnuth_involutive i

@[simp]
theorem weight_benderKnuth_left (i : Fin k) (T : SkewSemistandardYoungTableau (k + 1)) :
    (benderKnuth i T).weight i.castSucc = T.weight i.succ := by
  have hs := size_benderKnuthMiddle_add (T.interlaces i.castSucc) (T.interlaces i.succ)
  have hleft := (T.interlaces i.castSucc).size_le
  have hright := (T.interlaces i.succ).size_le
  change (benderKnuth i T i.castSucc.succ).size -
    (benderKnuth i T i.castSucc.castSucc).size =
      (T i.succ.succ).size - (T i.castSucc.succ).size
  rw [benderKnuth_apply_middle, benderKnuth_apply_of_ne _ _ _ (by simp [Fin.ext_iff])]
  simp only [Fin.castSucc_succ] at hs hright ⊢
  omega

@[simp]
theorem weight_benderKnuth_right (i : Fin k) (T : SkewSemistandardYoungTableau (k + 1)) :
    (benderKnuth i T).weight i.succ = T.weight i.castSucc := by
  have hs := size_benderKnuthMiddle_add (T.interlaces i.castSucc) (T.interlaces i.succ)
  have hleft := (T.interlaces i.castSucc).size_le
  have hright := (T.interlaces i.succ).size_le
  change (benderKnuth i T i.succ.succ).size -
    (benderKnuth i T i.castSucc.succ).size = _
  rw [benderKnuth_apply_middle, benderKnuth_apply_of_ne _ _ _ (by simp_all [Fin.ext_iff])]
  dsimp [weight]
  simp only [Fin.castSucc_succ] at hs hright ⊢
  omega

theorem weight_benderKnuth (i : Fin k) (T : SkewSemistandardYoungTableau (k + 1)) :
    (benderKnuth i T).weight = T.weight ∘ Equiv.swap i.castSucc i.succ := by
  funext j
  by_cases hl : j = i.castSucc
  · subst j
    simp
  · by_cases hr : j = i.succ
    · subst j
      simp
    · simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hl hr, weight]
      rw [benderKnuth_apply_of_ne _ _ _ (by simp_all [Fin.ext_iff]),
        benderKnuth_apply_of_ne _ _ _ (by simp_all [Fin.ext_iff])]

namespace WithWeight

/-- Bender–Knuth gives an equivalence between tableaux whose weights differ by
one adjacent transposition. -/
def benderKnuthEquiv (μ ν : IntegerPartition) (w : Fin (k + 1) → ℕ) (i : Fin k) :
    WithWeight μ ν w ≃ WithWeight μ ν (w ∘ Equiv.swap i.castSucc i.succ) where
  toFun T := ⟨benderKnuth i T.val, by
    simp only [innerShape_benderKnuth, outerShape_benderKnuth, weight_benderKnuth,
      T.innerShape_eq, T.outerShape_eq, T.weight_eq, and_self]⟩
  invFun T := ⟨benderKnuth i T.val, by
    refine ⟨by simp, by simp, ?_⟩
    rw [weight_benderKnuth, T.weight_eq]
    funext j
    simp⟩
  left_inv T := Subtype.ext (benderKnuth_involutive i T.val)
  right_inv T := Subtype.ext (benderKnuth_involutive i T.val)

end WithWeight

end SkewSemistandardYoungTableau
