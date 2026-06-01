import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.Antidiag.Prod

/-- A decomposable monoid is one where any element can only be decomposed
  into pairs of elements in finitely many ways. -/
class DecomposableAddMonoid (M : Type*) extends AddMonoid M where
  antidiagonal : M → Finset (M × M)
  mem_antidiagonal {m : M} {p : M × M} : p ∈ antidiagonal m ↔ p.1 + p.2 = m

namespace DecomposableAddMonoid

attribute [simp] mem_antidiagonal

variable {M : Type*} [DecomposableAddMonoid M] [DecidableEq M]

/-- The antidoublediagonal is the Finset of all triples (a, b, c) such that a + b + c = m. -/
def antidoublediagonal (m : M) : Finset (M × M × M) :=
  (antidiagonal m).biUnion fun p ↦
    (antidiagonal p.2).image fun q ↦ (p.1, q.1, q.2)

theorem mem_antidoublediagonal' (m : M) {a b c : M} :
    (a, b, c) ∈ antidoublediagonal m ↔ ∃ p : M,
    (a, p) ∈ antidiagonal m ∧ (b, c) ∈ antidiagonal p := by
  simp [antidoublediagonal]

@[simp]
theorem mem_antidoublediagonal (m : M) {a b c : M} :
    (a, b, c) ∈ antidoublediagonal m ↔ a + b + c = m := by
  simp [mem_antidoublediagonal', add_assoc]

theorem mem_antidoublediagonal'' (m : M) {a b c : M} :
    (a, b, c) ∈ antidoublediagonal m ↔ ∃ q : M,
    (q, c) ∈ antidiagonal m ∧ (a, b) ∈ antidiagonal q := by
  simp

lemma antidoublediagonal_eq_alt (m : M) :
  antidoublediagonal m = (antidiagonal m).biUnion fun p ↦
    (antidiagonal p.1).image fun q ↦ (q.1, q.2, p.2) := by
  ext ⟨a, b, c⟩
  rw [mem_antidoublediagonal'']
  simp only [Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨q, h1, h2⟩
    exact ⟨(q, c), h1, (a, b), h2, rfl⟩
  · rintro ⟨⟨q, c'⟩, h1, ⟨a', b'⟩, h2, heq⟩
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl, rfl⟩
    exact ⟨q, h1, h2⟩

/-- Summing over all triples in the antidoublediagonal can be expressed as a
  double sum involving the antidiagonal. This can be done in two different ways,
  which is useful for proving associativity in the total monoid algebra. -/
theorem antidoublediagonal_fst_sum {R : Type*} [AddCommMonoid R]
  (f : M → M → M → R) (m : M) :
  ∑ s ∈ antidoublediagonal m, f s.1 s.2.1 s.2.2 =
  ∑ p ∈ antidiagonal m, ∑ q ∈ antidiagonal p.2, f p.1 q.1 q.2 := by
  unfold antidoublediagonal
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_image]
    · intro y _ z _ hyz
      simp only [Prod.mk.injEq] at hyz
      ext
      · exact hyz.2.1
      · exact hyz.2.2
  · intro x _ y _ hxy
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image]
    rintro _ ⟨⟨q1a, q1b⟩, hq1, rfl⟩ ⟨⟨q2a, q2b⟩, hq2, h2⟩
    simp only [Prod.mk.injEq] at h2
    simp only [mem_antidiagonal] at hq1 hq2
    have : x = y := by
      ext
      · exact h2.1.symm
      · rw [← hq1, ← hq2, h2.2.1, h2.2.2]
    exact hxy this

theorem antidoublediagonal_snd_sum {R : Type*} [AddCommMonoid R]
  (f : M → M → M → R) (m : M) :
  ∑ s ∈ antidoublediagonal m, f s.1 s.2.1 s.2.2 =
  ∑ p ∈ antidiagonal m, ∑ q ∈ antidiagonal p.1, f q.1 q.2 p.2 := by
  rw [antidoublediagonal_eq_alt m]
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_image]
    · intro y _ z _ hyz
      simp only [Prod.mk.injEq] at hyz
      ext
      · exact hyz.1
      · exact hyz.2.1
  · intro x _ y _ hxy
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image]
    rintro _ ⟨⟨q1a, q1b⟩, hq1, rfl⟩ ⟨⟨q2a, q2b⟩, hq2, h2⟩
    simp only [Prod.mk.injEq] at h2
    simp only [mem_antidiagonal] at hq1 hq2
    have : x = y := by
      ext
      · rw [← hq1, ← hq2, h2.1, h2.2.1]
      · exact h2.2.2.symm
    exact hxy this

end DecomposableAddMonoid
