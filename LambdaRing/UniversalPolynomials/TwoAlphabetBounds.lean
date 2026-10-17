import LambdaRing.UniversalPolynomials.TwoAlphabets

/-! # Injectivity of elementary substitution in two finite blocks -/

namespace LambdaRing.UniversalPolynomial

noncomputable section

open MvPolynomial

variable (R : Type*) [CommRing R]

/-- Elementary substitution in the right finite block, fixing the left block. -/
def rightElementary (N M : ℕ) :
    MvPolynomial (Fin N ⊕ Fin M) R →ₐ[R] MvPolynomial (Fin N ⊕ Fin M) R :=
  aeval (Sum.elim (fun i : Fin N => X (Sum.inl i))
    (fun j : Fin M => rename Sum.inr (esymm (Fin M) R (j.val + 1))))

/-- Exchanging the two blocks turns right elementary substitution into left substitution. -/
theorem rename_swap_rightElementary (N M : ℕ) :
    (rename Sum.swap).comp (rightElementary R N M) =
      (leftElementary R M (Fin N)).comp (rename Sum.swap) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i <;> simp [rightElementary, leftElementary, rename_rename, Function.comp_def]

theorem rightElementary_injective (N M : ℕ) :
    Function.Injective (rightElementary R N M) := by
  intro p q hpq
  apply rename_injective (Sum.swap : Fin N ⊕ Fin M → Fin M ⊕ Fin N)
    (Equiv.sumComm (Fin N) (Fin M)).injective
  apply leftElementary_injective R M (Fin N)
  have hp := DFunLike.congr_fun (rename_swap_rightElementary R N M) p
  have hq := DFunLike.congr_fun (rename_swap_rightElementary R N M) q
  exact hp.symm.trans ((congrArg (rename Sum.swap) hpq).trans hq)

/-- Left substitution fixes any polynomial entirely in the right block. -/
theorem leftElementary_rename_right (N : ℕ) (τ : Type*) (q : MvPolynomial τ R) :
    leftElementary R N τ (rename Sum.inr q) = rename Sum.inr q := by
  unfold leftElementary
  rw [aeval_rename]
  conv_rhs => rw [rename_eq_aeval]
  rfl

/-- Simultaneous elementary substitution in both finite blocks is injective. -/
theorem twoElementary_injective (N M : ℕ) :
    Function.Injective (aeval (R := R) (Sum.elim
      (fun i : Fin N => rename Sum.inl (esymm (Fin N) R (i.val + 1)))
      (fun j : Fin M => rename Sum.inr (esymm (Fin M) R (j.val + 1))))) := by
  have he : (leftElementary R N (Fin M)).comp (rightElementary R N M) =
      aeval (Sum.elim
        (fun i : Fin N => rename Sum.inl (esymm (Fin N) R (i.val + 1)))
        (fun j : Fin M => rename Sum.inr (esymm (Fin M) R (j.val + 1)))) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | inl i => simp [rightElementary, leftElementary]
    | inr j =>
      simp only [AlgHom.comp_apply, rightElementary, aeval_X, Sum.elim_inr]
      exact leftElementary_rename_right R N (Fin M) _
  rw [← he]
  exact (leftElementary_injective R N (Fin M)).comp (rightElementary_injective R N M)

/-- The first N positive indices, in the fixed increasing order. -/
def positiveIndexEmbedding (N : ℕ) : Fin N ↪ ℕ+ where
  toFun i := Nat.succPNat i.val
  inj' _i _j he := Fin.ext (Nat.succ_inj.mp (congrArg PNat.val he))

theorem mem_range_positiveIndexEmbedding (N : ℕ) (i : ℕ+) :
    i ∈ Set.range (positiveIndexEmbedding N) ↔ (i : ℕ) ≤ N := by
  constructor
  · rintro ⟨j, rfl⟩
    exact j.isLt
  · intro hi
    refine ⟨⟨(i : ℕ) - 1, by have := i.pos; omega⟩, ?_⟩
    apply PNat.coe_injective
    change (i : ℕ) - 1 + 1 = (i : ℕ)
    have := i.pos
    omega

/-- Every bounded two-block expression comes from the corresponding finite index sets. -/
theorem exists_rename_positiveBlocks (N M : ℕ) (q : MvPolynomial (ℕ+ ⊕ ℕ+) R)
    (hl : ∀ i, Sum.inl i ∈ q.vars → (i : ℕ) ≤ N)
    (hr : ∀ j, Sum.inr j ∈ q.vars → (j : ℕ) ≤ M) :
    ∃ p : MvPolynomial (Fin N ⊕ Fin M) R,
      rename ((positiveIndexEmbedding N).sumMap (positiveIndexEmbedding M)) p = q := by
  apply exists_rename_eq_of_vars_subset_range _ _ (Function.Embedding.injective _)
  intro k hk
  cases k with
  | inl i =>
    obtain ⟨j, hj⟩ := (mem_range_positiveIndexEmbedding N i).mpr (hl i hk)
    exact ⟨Sum.inl j, congrArg Sum.inl hj⟩
  | inr i =>
    obtain ⟨j, hj⟩ := (mem_range_positiveIndexEmbedding M i).mpr (hr i hk)
    exact ⟨Sum.inr j, congrArg Sum.inr hj⟩

/-- Both finite alphabets determine a polynomial whose indices fit within their sizes. -/
theorem twoElementary_injective_of_vars_le (N M : ℕ)
    {q r : MvPolynomial (ℕ+ ⊕ ℕ+) R}
    (hql : ∀ i, Sum.inl i ∈ q.vars → (i : ℕ) ≤ N)
    (hqr : ∀ j, Sum.inr j ∈ q.vars → (j : ℕ) ≤ M)
    (hrl : ∀ i, Sum.inl i ∈ r.vars → (i : ℕ) ≤ N)
    (hrr : ∀ j, Sum.inr j ∈ r.vars → (j : ℕ) ≤ M)
    (he : aeval (Sum.elim (fun i : ℕ+ => rename Sum.inl (esymm (Fin N) R i))
        (fun j : ℕ+ => rename Sum.inr (esymm (Fin M) R j))) q =
      aeval (Sum.elim (fun i : ℕ+ => rename Sum.inl (esymm (Fin N) R i))
        (fun j : ℕ+ => rename Sum.inr (esymm (Fin M) R j))) r) : q = r := by
  obtain ⟨p, rfl⟩ := exists_rename_positiveBlocks R N M q hql hqr
  obtain ⟨s, rfl⟩ := exists_rename_positiveBlocks R N M r hrl hrr
  congr 1
  apply twoElementary_injective R N M
  have hf : (Sum.elim (fun i : ℕ+ => rename Sum.inl (esymm (Fin N) R i))
      (fun j : ℕ+ => rename Sum.inr (esymm (Fin M) R j))) ∘
      ((positiveIndexEmbedding N).sumMap (positiveIndexEmbedding M)) =
      Sum.elim (fun i : Fin N => rename Sum.inl (esymm (Fin N) R (i.val + 1)))
        (fun j : Fin M => rename Sum.inr (esymm (Fin M) R (j.val + 1))) := by
    funext k
    cases k <;> rfl
  simpa only [aeval_rename, hf] using he

end

end LambdaRing.UniversalPolynomial
