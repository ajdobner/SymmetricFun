import LambdaRing.UniversalPolynomials.Finite

/-! # Squarefree monomial alphabets, including the degree-zero singleton -/

namespace LambdaRing.UniversalPolynomial

noncomputable section

open Finset

variable {σ τ A B : Type*} [Fintype σ] [Fintype τ] [CommSemiring A] [CommSemiring B]

/-- The squarefree degree-m alphabet is indexed by m-element subsets. -/
abbrev SquarefreeIndex (σ : Type*) [Fintype σ] (m : ℕ) :=
  ↥((Finset.univ : Finset σ).powersetCard m)

/-- Evaluate the squarefree monomial indexed by a subset. -/
def squarefreeValue (x : σ → A) {m : ℕ} (s : SquarefreeIndex σ m) : A :=
  ∏ i ∈ s.val, x i

/-- An embedding of variables induces an embedding of squarefree alphabets. -/
def squarefreeEmbedding (f : σ ↪ τ) (m : ℕ) : SquarefreeIndex σ m ↪ SquarefreeIndex τ m where
  toFun s := ⟨s.val.map f, by simpa only [mem_powersetCard, subset_univ, card_map, true_and]
    using (mem_powersetCard.mp s.property).2⟩
  inj' s t h := Subtype.ext ((Finset.map_injective f) (congrArg Subtype.val h))

@[simp] theorem squarefreeEmbedding_val (f : σ ↪ τ) (m : ℕ) (s : SquarefreeIndex σ m) :
    (squarefreeEmbedding f m s).val = s.val.map f := rfl

/-- The range consists exactly of subsets whose entries all lie in the original alphabet. -/
theorem range_squarefreeEmbedding (f : σ ↪ τ) (m : ℕ) (s : SquarefreeIndex τ m) :
    s ∈ Set.range (squarefreeEmbedding f m) ↔ ∀ j ∈ s.val, j ∈ Set.range f := by
  classical
  constructor
  · rintro ⟨t, rfl⟩ j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hj
    exact ⟨i, rfl⟩
  · intro h
    let t := (univ : Finset σ).filter (fun i => f i ∈ s.val)
    have ht : t.map f = s.val := by
      ext j
      simp only [Finset.mem_map, mem_filter, mem_univ, true_and, t]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact hi
      · intro hj
        obtain ⟨i, rfl⟩ := h j hj
        exact ⟨i, hj, rfl⟩
    have hc : t.card = m := by
      rw [← Finset.card_map f, ht]
      exact (mem_powersetCard.mp s.property).2
    exact ⟨⟨t, mem_powersetCard.mpr ⟨subset_univ _, hc⟩⟩, Subtype.ext ht⟩

@[simp] theorem squarefreeValue_embedding (f : σ ↪ τ) (y : τ → A)
    (m : ℕ) (s : SquarefreeIndex σ m) :
    squarefreeValue y (squarefreeEmbedding f m s) = squarefreeValue (y ∘ f) s := by
  simp [squarefreeValue]

@[simp] theorem map_squarefreeValue (φ : A →+* B) (x : σ → A)
    {m : ℕ} (s : SquarefreeIndex σ m) :
    φ (squarefreeValue x s) = squarefreeValue (φ ∘ x) s := by
  simp [squarefreeValue]

/-- Iterating elementary evaluation on the squarefree degree-m alphabet. -/
def iterationValue (x : σ → A) (n m : ℕ) : A :=
  elementaryValue (squarefreeValue x (m := m)) n

@[simp] theorem map_iterationValue (φ : A →+* B) (x : σ → A) (n m : ℕ) :
    φ (iterationValue x n m) = iterationValue (φ ∘ x) n m := by
  unfold iterationValue
  rw [map_elementaryValue]
  congr 1
  funext s
  exact map_squarefreeValue φ x s

/-- Adjoining zero variables preserves every squarefree iteration, also for m=0. -/
theorem iterationValue_extend (f : σ ↪ τ) (x : σ → A) (y : τ → A)
    (hxy : ∀ i, y (f i) = x i) (hz : ∀ j, j ∉ Set.range f → y j = 0) (n m : ℕ) :
    iterationValue y n m = iterationValue x n m := by
  classical
  apply elementaryValue_extend (squarefreeEmbedding f m)
  · intro s
    rw [squarefreeValue_embedding]
    congr 1
    exact funext hxy
  · intro s hs
    have hn : ¬ ∀ j ∈ s.val, j ∈ Set.range f :=
      fun h => hs ((range_squarefreeEmbedding f m s).mpr h)
    push Not at hn
    obtain ⟨j, hjs, hj⟩ := hn
    exact Finset.prod_eq_zero hjs (hz j hj)

/-- Reindexing variables preserves squarefree iteration. -/
theorem iterationValue_equiv (f : σ ≃ τ) (y : τ → A) (n m : ℕ) :
    iterationValue (y ∘ f) n m = iterationValue y n m := by
  symm
  exact iterationValue_extend f.toEmbedding _ _ (fun _ => rfl)
    (fun j hj => False.elim (hj (f.surjective j))) n m

@[simp] theorem iterationValue_zero (x : σ → A) (m : ℕ) : iterationValue x 0 m = 1 := by
  simp [iterationValue]

@[simp] theorem iterationValue_one (x : σ → A) (m : ℕ) :
    iterationValue x 1 m = elementaryValue x m := by
  rw [iterationValue, elementaryValue_one]
  simp only [univ_eq_attach]
  exact Finset.sum_attach _ (fun s : Finset σ => ∏ i ∈ s, x i)

/-- The degree-zero squarefree alphabet has one entry, with value one. -/
theorem iterationValue_zero_right (x : σ → A) (n : ℕ) :
    iterationValue x n 0 = if n ≤ 1 then 1 else 0 := by
  classical
  by_cases hn : n ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
    · simp
    · simp
  · simp only [hn, ↓reduceIte]
    apply elementaryValue_eq_zero_of_card_lt
    simpa only [SquarefreeIndex, Fintype.card_coe, card_powersetCard, Nat.choose_zero_right]
      using Nat.lt_of_not_ge hn

/-- Singleton subsets identify the squarefree degree-one alphabet with the variables. -/
def singletonSquarefreeEquiv : σ ≃ SquarefreeIndex σ 1 := by
  classical
  apply Equiv.ofBijective (fun i => ⟨{i}, by simp⟩)
  constructor
  · intro i j he
    exact Finset.singleton_injective (congrArg Subtype.val he)
  · intro s
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (mem_powersetCard.mp s.property).2
    exact ⟨i, Subtype.ext hi.symm⟩

@[simp] theorem singletonSquarefreeEquiv_val (i : σ) :
    (singletonSquarefreeEquiv i : Finset σ) = {i} := rfl

@[simp] theorem iterationValue_one_right (x : σ → A) (n : ℕ) :
    iterationValue x n 1 = elementaryValue x n := by
  have he := elementaryValue_equiv (singletonSquarefreeEquiv (σ := σ))
    (squarefreeValue x) n
  have hx : squarefreeValue x ∘ singletonSquarefreeEquiv = x := by
    funext i
    simp [squarefreeValue]
  rw [hx] at he
  exact he.symm

/-- Squarefree iteration polynomials in the original alphabet variables. -/
def iterationFinite (σ R : Type*) [Fintype σ] [CommSemiring R] (n m : ℕ) :
    MvPolynomial σ R := iterationValue MvPolynomial.X n m

@[simp] theorem map_iterationFinite (φ : A →+* B) (n m : ℕ) :
    MvPolynomial.map φ (iterationFinite σ A n m) = iterationFinite σ B n m := by
  change MvPolynomial.map φ (iterationValue MvPolynomial.X n m) = _
  rw [map_iterationValue]
  congr 1
  funext i
  simp

/-- The finite iteration expression is symmetric in the original variables. -/
theorem iterationFinite_isSymmetric (R : Type*) [CommSemiring R] (n m : ℕ) :
    MvPolynomial.IsSymmetric (iterationFinite σ R n m) := by
  intro e
  change (MvPolynomial.rename e).toRingHom (iterationValue MvPolynomial.X n m) = _
  rw [map_iterationValue]
  have he : (MvPolynomial.rename (R := R) e).toRingHom ∘ MvPolynomial.X = MvPolynomial.X ∘ e := by
    funext i
    simp
  rw [he]
  exact iterationValue_equiv e _ n m

/-- Its alphabet degree is n*m, including the degree-zero boundary cases. -/
theorem iterationFinite_isHomogeneous (R : Type*) [CommSemiring R] (n m : ℕ) :
    (iterationFinite σ R n m).IsHomogeneous (n * m) := by
  apply isHomogeneous_elementaryValue _ m n
  intro s
  have hp := MvPolynomial.IsHomogeneous.prod s.val (fun i : σ => MvPolynomial.X (R := R) i)
    (fun _ => 1) (fun i _ => MvPolynomial.isHomogeneous_X R i)
  simpa [squarefreeValue, (mem_powersetCard.mp s.property).2] using hp

/-- Setting the last variable to zero preserves every finite iteration expression. -/
theorem zeroLast_iterationFinite (R : Type*) [CommSemiring R] (N n m : ℕ) :
    SymmetricFunction.zeroLast R N (iterationFinite (Fin (N + 1)) R n m) =
      iterationFinite (Fin N) R n m := by
  change (SymmetricFunction.zeroLast R N).toRingHom
    (iterationValue MvPolynomial.X n m) = _
  rw [map_iterationValue]
  apply iterationValue_extend Fin.castSuccEmb
  · intro i
    simp
  · intro j
    refine Fin.lastCases ?_ ?_ j
    · intro _
      simp
    · intro i hi
      exact False.elim (hi ⟨i, rfl⟩)

end

end LambdaRing.UniversalPolynomial
