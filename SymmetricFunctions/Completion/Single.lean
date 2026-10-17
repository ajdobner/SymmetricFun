import SymmetricFunctions.Completion.Graded

/-! # Single-degree elements of a graded completion -/
noncomputable section
namespace SymmetricFunctions.GradedCompletion
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (G : ℕ → Submodule R A) [SetLike.GradedMonoid G]

/-- Place a homogeneous element at its degree and zero elsewhere. -/
def single (n : ℕ) (a : A) (ha : a ∈ G n) : GradedCompletion G :=
  fun k => ⟨if k = n then a else 0, by
    split_ifs with h
    · simpa only [h] using ha
    · exact (G k).zero_mem⟩

omit [SetLike.GradedMonoid G] in
@[simp] theorem component_single (n : ℕ) (a : A) (ha : a ∈ G n) (k : ℕ) :
    component G (single G n a ha) k = if k = n then a else 0 := rfl

@[simp] theorem toPowerSeries_single (n : ℕ) (a : A) (ha : a ∈ G n) :
    toPowerSeries G (single G n a ha) = PowerSeries.monomial n a := by
  ext k
  rw [coeff_toPowerSeries, component_single, PowerSeries.coeff_monomial]

/-- Multiplying single-degree elements adds their degrees. -/
theorem single_mul_single (i j : ℕ) (a b : A) (ha : a ∈ G i) (hb : b ∈ G j) :
    single G i a ha * single G j b hb =
      single G (i + j) (a * b) (SetLike.GradedMul.mul_mem ha hb) := by
  apply toPowerSeries_injective G
  rw [map_mul, toPowerSeries_single, toPowerSeries_single,
    toPowerSeries_single, PowerSeries.monomial_mul_monomial]

/-- A degree-preserving map sends a single-degree element to the matching single. -/
theorem map_single {B : Type*} [CommRing B] [Algebra R B]
    (H : ℕ → Submodule R B) [SetLike.GradedMonoid H] (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ G n → φ a ∈ H n) (n : ℕ) (a : A) (ha : a ∈ G n) :
    map G H φ hφ (single G n a ha) = single H n (φ a) (hφ n a ha) := by
  apply ext H
  intro k
  rw [component_map, component_single, component_single]
  split_ifs <;> simp

end SymmetricFunctions.GradedCompletion
