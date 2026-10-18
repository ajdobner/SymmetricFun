module

public import SymmetricFun.Tableau.BenderKnuth
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Equiv.Fintype

/-!
# Skew Kostka numbers

We first count skew semistandard tableaux with a weak composition as weight. Bender–Knuth
involutions prove that permuting the weight entries preserves the count. Unused labels
can also be removed, so the count depends only on the integer partition formed
by the nonzero weight entries. `skewKostkaWeight_removeNth_zero` removes a single
zero entry using `Fin.removeNth`.

The public counting functions take `Nat.Partition` arguments with independent
size indices. Tableau chains use `IntegerPartition` internally; no equality
between the shape and weight sizes is required to form a Kostka number.
-/

@[expose] public section

open SkewSemistandardYoungTableau

namespace Nat.Partition

variable {n m d : ℕ}

/-- The number of skew tableaux of shape `π / μ` and weak composition weight `w`. -/
noncomputable def skewKostkaWeight {k : ℕ}
    (π : Nat.Partition n) (μ : Nat.Partition m) (w : Fin k → ℕ) : ℕ :=
  Nat.card (WithWeight μ.toIntegerPartition π.toIntegerPartition w)

theorem skewKostkaWeight_swap {k : ℕ} (π : Nat.Partition n) (μ : Nat.Partition m)
    (w : Fin (k + 1) → ℕ) (i : Fin k) :
    skewKostkaWeight π μ (w ∘ Equiv.swap i.castSucc i.succ) =
      skewKostkaWeight π μ w :=
  Nat.card_congr (WithWeight.benderKnuthEquiv μ.toIntegerPartition π.toIntegerPartition w i).symm

/-- The tableau count is invariant under every permutation of the weight entries. -/
theorem skewKostkaWeight_perm {k : ℕ} (π : Nat.Partition n) (μ : Nat.Partition m)
    (w : Fin k → ℕ) (e : Equiv.Perm (Fin k)) :
    skewKostkaWeight π μ (w ∘ e) = skewKostkaWeight π μ w := by
  cases k with
  | zero =>
    congr 1
    funext i
    exact Fin.elim0 i
  | succ k =>
    have he : e ∈ Submonoid.closure
        (Set.range fun i : Fin k => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    induction he using Submonoid.closure_induction generalizing w with
    | mem e he =>
      obtain ⟨i, rfl⟩ := he
      exact skewKostkaWeight_swap π μ w i
    | one => rfl
    | mul a b ha hb ia ib =>
      change skewKostkaWeight π μ ((w ∘ a) ∘ b) = _
      rw [ib, ia]

theorem skewKostkaWeight_reindex {k l : ℕ} (π : Nat.Partition n) (μ : Nat.Partition m)
    (w : Fin l → ℕ) (e : Fin k ≃ Fin l) :
    skewKostkaWeight π μ (w ∘ e) = skewKostkaWeight π μ w := by
  have h : k = l := by simpa using Fintype.card_congr e
  subst l
  exact skewKostkaWeight_perm π μ w e

@[simp]
theorem skewKostkaWeight_append_zero {k : ℕ}
    (π : Nat.Partition n) (μ : Nat.Partition m) (w : Fin k → ℕ) :
    skewKostkaWeight π μ (Fin.lastCases 0 w) = skewKostkaWeight π μ w :=
  Nat.card_congr (WithWeight.appendZeroEquiv μ.toIntegerPartition π.toIntegerPartition w).symm

/-- Removing an unused label preserves the number of tableaux. -/
theorem skewKostkaWeight_removeNth_zero {k : ℕ} (π : Nat.Partition n) (μ : Nat.Partition m)
    (w : Fin (k + 1) → ℕ) (i : Fin (k + 1)) (hi : w i = 0) :
    skewKostkaWeight π μ (i.removeNth w) = skewKostkaWeight π μ w := by
  let e := (finSuccEquiv' (Fin.last k)).trans (finSuccEquiv' i).symm
  have he : w ∘ e = Fin.lastCases 0 (i.removeNth w) := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa [e] using hi
    · simp [e, finSuccEquiv'_last_apply_castSucc, Fin.removeNth]
  have h := skewKostkaWeight_perm π μ w e
  rwa [he, skewKostkaWeight_append_zero] at h

private theorem exists_equiv_of_multiset_eq {k l : ℕ} (w : Fin k → ℕ) (v : Fin l → ℕ)
    (h : (List.ofFn w : Multiset ℕ) = (List.ofFn v : Multiset ℕ)) :
    ∃ e : Fin k ≃ Fin l, w = v ∘ e := by
  classical
  have hc (a : ℕ) : Fintype.card {i // w i = a} = Fintype.card {i // v i = a} := by
    have hh := congrArg (Multiset.count a) h
    simpa only [← Fin.univ_val_map, Multiset.count_map, eq_comm (a := a),
      Fintype.card_subtype, Finset.card_def, Finset.filter_val] using hh
  let e := Equiv.ofFiberEquiv (fun a => Fintype.equivOfCardEq (hc a))
  exact ⟨e, funext fun i => (Equiv.ofFiberEquiv_map _ i).symm⟩

/-- The skew Kostka number of shape `π / μ` and partition weight `ν`.
The shape and weight sizes are independent; incompatible sizes give zero. -/
noncomputable def skewKostka
    (π : Nat.Partition n) (μ : Nat.Partition m) (ν : Nat.Partition d) : ℕ :=
  skewKostkaWeight π μ (ν.parts.sort (· ≥ ·)).get

/-- The ordinary Kostka number is the skew count with empty inner shape. -/
noncomputable def kostka (π : Nat.Partition n) (ν : Nat.Partition d) : ℕ :=
  skewKostka π (default : Nat.Partition 0) ν

/-- Passing from a weak composition weight to its integer partition preserves the count,
including when the weight contains zero entries. -/
theorem skewKostkaWeight_eq_skewKostka {k : ℕ}
    (π : Nat.Partition n) (μ : Nat.Partition m) (w : Fin k → ℕ) :
    skewKostkaWeight π μ w = skewKostka π μ (IntegerPartition.ofFn w).2 := by
  change skewKostkaWeight π μ w =
    skewKostkaWeight π μ ((IntegerPartition.ofFn w).parts.sort (· ≥ ·)).get
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hz : ∃ i, w i = 0
    · obtain ⟨i, hi⟩ := hz
      cases k with
      | zero => exact Fin.elim0 i
      | succ k =>
        rw [← skewKostkaWeight_removeNth_zero π μ w i hi,
          ih k (Nat.lt_succ_self k), IntegerPartition.ofFn_removeNth_of_eq_zero w i hi]
    · have hp : (IntegerPartition.ofFn w).parts = (List.ofFn w : Multiset ℕ) := by
        rw [IntegerPartition.parts_ofFn, Multiset.filter_eq_self]
        intro a ha
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp ha)
        exact fun hi => hz ⟨i, hi⟩
      obtain ⟨e, he⟩ := exists_equiv_of_multiset_eq w
        ((IntegerPartition.ofFn w).parts.sort (· ≥ ·)).get (by
          rw [List.ofFn_get, Multiset.sort_eq, hp])
      exact (congrArg (skewKostkaWeight π μ) he).trans
        (skewKostkaWeight_reindex π μ _ e)

/-- Weak composition weights of different lengths give the same count whenever their
nonzero entries form the same integer partition. -/
theorem skewKostkaWeight_eq_of_ofFn_eq {k l : ℕ}
    (π : Nat.Partition n) (μ : Nat.Partition m)
    {w : Fin k → ℕ} {v : Fin l → ℕ} (h : IntegerPartition.ofFn w = IntegerPartition.ofFn v) :
    skewKostkaWeight π μ w = skewKostkaWeight π μ v := by
  rw [skewKostkaWeight_eq_skewKostka, skewKostkaWeight_eq_skewKostka, h]

theorem skewKostkaWeight_empty_inner {k : ℕ} (π : Nat.Partition n) (w : Fin k → ℕ) :
    skewKostkaWeight π (default : Nat.Partition 0) w = kostka π (IntegerPartition.ofFn w).2 :=
  skewKostkaWeight_eq_skewKostka π default w

/-- There is exactly one empty tableau on each fixed alphabet. -/
@[simp]
theorem skewKostkaWeight_self_zero {k : ℕ} (μ : Nat.Partition n) :
    skewKostkaWeight μ μ (0 : Fin k → ℕ) = 1 :=
  Nat.card_of_subsingleton (WithWeight.const k μ.toIntegerPartition)

@[simp]
theorem skewKostka_self_empty (μ : Nat.Partition n) :
    skewKostka μ μ (default : Nat.Partition 0) = 1 := by
  unfold skewKostka
  rw [partition_zero_parts (default : Nat.Partition 0), Multiset.sort_zero]
  have hw : ([] : List ℕ).get = (0 : Fin 0 → ℕ) := funext fun i => Fin.elim0 i
  rw [hw]
  exact skewKostkaWeight_self_zero μ

/-- The total weight must equal the size of the skew shape. -/
theorem skewKostkaWeight_eq_zero_of_size_ne {k : ℕ}
    (π : Nat.Partition n) (μ : Nat.Partition m)
    (w : Fin k → ℕ) (h : m + ∑ i, w i ≠ n) :
    skewKostkaWeight π μ w = 0 := by
  let := WithWeight.isEmpty_of_size_ne (μ := μ.toIntegerPartition)
    (ν := π.toIntegerPartition) h
  exact Nat.card_of_isEmpty

theorem skewKostka_eq_zero_of_size_ne
    (π : Nat.Partition n) (μ : Nat.Partition m) (ν : Nat.Partition d)
    (h : m + d ≠ n) : skewKostka π μ ν = 0 := by
  have hv : ∑ i, (ν.parts.sort (· ≥ ·)).get i = d := by
    rw [← List.sum_ofFn, List.ofFn_get, ← Multiset.sum_coe, Multiset.sort_eq, ν.parts_sum]
  apply skewKostkaWeight_eq_zero_of_size_ne
  simpa only [hv] using h

theorem kostka_eq_zero_of_size_ne (π : Nat.Partition n) (ν : Nat.Partition d) (h : d ≠ n) :
    kostka π ν = 0 :=
  skewKostka_eq_zero_of_size_ne π default ν (by simpa using h)

end Nat.Partition
