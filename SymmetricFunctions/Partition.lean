import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.PNat.Defs

/-!
# Partitions as weighted exponent vectors

This adapter uses Mathlib's `Nat.Partition`. The exponent at the positive index
`i` is the multiplicity of the part `i`, and its weight is the size of the
partition. No replacement partition type is introduced.
-/

namespace SymmetricFunctions.Partition

open scoped BigOperators

variable {d : ℕ}

/-- The positive parts of a partition, retaining their multiplicities. -/
def positiveParts (μ : Nat.Partition d) : Multiset ℕ+ :=
  μ.parts.attach.map fun i => Nat.toPNat i.val (μ.parts_pos i.property)

@[simp] theorem map_positiveParts (μ : Nat.Partition d) :
    (positiveParts μ).map (fun i : ℕ+ => (i : ℕ)) = μ.parts := by
  unfold positiveParts
  rw [Multiset.map_map]
  exact Multiset.attach_map_val _

/-- The multiplicity vector of the positive parts. -/
def toExponents (μ : Nat.Partition d) : ℕ+ →₀ ℕ :=
  (positiveParts μ).toFinsupp

@[simp] theorem toExponents_apply (μ : Nat.Partition d) (i : ℕ+) :
    toExponents μ i = μ.parts.count (i : ℕ) := by
  rw [toExponents, Multiset.toFinsupp_apply, ← map_positiveParts μ]
  exact (Multiset.count_map_eq_count' (fun j : ℕ+ => (j : ℕ)) _
    PNat.coe_injective i).symm

@[simp] theorem toMultiset_toExponents (μ : Nat.Partition d) :
    (toExponents μ).toMultiset = positiveParts μ :=
  Multiset.toFinsupp_toMultiset _

/-- Expanding multiplicities computes weighted size, not the number of parts. -/
theorem sum_toMultiset (a : ℕ+ →₀ ℕ) :
    (a.toMultiset.map (fun i : ℕ+ => (i : ℕ))).sum =
      ∑ i ∈ a.support, (i : ℕ) * a i := by
  rw [Finsupp.toMultiset_map, Finsupp.sum_toMultiset]
  rw [Finsupp.sum_mapDomain_index (fun b => zero_nsmul b) (fun b m n => add_nsmul b m n)]
  simp [Finsupp.sum, Nat.mul_comm]

theorem weight_toExponents (μ : Nat.Partition d) :
    ∑ i ∈ (toExponents μ).support, (i : ℕ) * toExponents μ i = d := by
  rw [← sum_toMultiset, toMultiset_toExponents, map_positiveParts, μ.parts_sum]

/-- Convert Mathlib's scalar-weight convention to the explicit weighted sum. -/
theorem weight_eq_sum (a : ℕ+ →₀ ℕ) :
    a.weight (fun i : ℕ+ => (i : ℕ)) = ∑ i ∈ a.support, (i : ℕ) * a i := by
  simp [Finsupp.weight_apply, Finsupp.sum, Nat.mul_comm]

/-- Compatibility with the weight convention used by Mathlib's graded polynomials. -/
theorem finsupp_weight_toExponents (μ : Nat.Partition d) :
    (toExponents μ).weight (fun i : ℕ+ => (i : ℕ)) = d := by
  rw [weight_eq_sum, weight_toExponents]

/-- Expand a weighted exponent vector into a partition of its specified weight. -/
def ofExponents (a : ℕ+ →₀ ℕ)
    (ha : ∑ i ∈ a.support, (i : ℕ) * a i = d) : Nat.Partition d where
  parts := a.toMultiset.map (fun i : ℕ+ => (i : ℕ))
  parts_pos := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hi
    exact j.pos
  parts_sum := (sum_toMultiset a).trans ha

@[simp] theorem ofExponents_parts (a : ℕ+ →₀ ℕ)
    (ha : ∑ i ∈ a.support, (i : ℕ) * a i = d) :
    (ofExponents a ha).parts = a.toMultiset.map (fun i : ℕ+ => (i : ℕ)) := rfl

@[simp] theorem ofExponents_toExponents (μ : Nat.Partition d) :
    ofExponents (toExponents μ) (weight_toExponents μ) = μ := by
  apply Nat.Partition.ext
  simp

@[simp] theorem toExponents_ofExponents (a : ℕ+ →₀ ℕ)
    (ha : ∑ i ∈ a.support, (i : ℕ) * a i = d) :
    toExponents (ofExponents a ha) = a := by
  ext i
  rw [toExponents_apply, ofExponents_parts,
    Multiset.count_map_eq_count' (fun j : ℕ+ => (j : ℕ)) _
      PNat.coe_injective, Finsupp.count_toMultiset]

/-- Partitions of `d` are exactly positive-index exponent vectors of weight `d`. -/
def exponentEquiv (d : ℕ) : Nat.Partition d ≃
    {a : ℕ+ →₀ ℕ // ∑ i ∈ a.support, (i : ℕ) * a i = d} where
  toFun μ := ⟨toExponents μ, weight_toExponents μ⟩
  invFun a := ofExponents a.val a.property
  left_inv := ofExponents_toExponents
  right_inv a := Subtype.ext (toExponents_ofExponents a.val a.property)

/-- The same equivalence in the index type used by weighted homogeneous monomials. -/
noncomputable def weightedExponentEquiv (d : ℕ) : Nat.Partition d ≃
    {a : ℕ+ →₀ ℕ // a.weight (fun i : ℕ+ => (i : ℕ)) = d} :=
  (exponentEquiv d).trans (Equiv.subtypeEquivRight fun a => by rw [weight_eq_sum])

@[simp] theorem weightedExponentEquiv_apply (μ : Nat.Partition d) :
    (weightedExponentEquiv d μ).val = toExponents μ := rfl

@[simp] theorem exponentEquiv_apply (μ : Nat.Partition d) :
    (exponentEquiv d μ).val = toExponents μ := rfl

@[simp] theorem exponentEquiv_symm_apply
    (a : {a : ℕ+ →₀ ℕ // ∑ i ∈ a.support, (i : ℕ) * a i = d}) :
    (exponentEquiv d).symm a = ofExponents a.val a.property := rfl

/-- A product indexed by parts is the product of the corresponding powers. -/
theorem prod_parts {M : Type*} [CommMonoid M] (μ : Nat.Partition d) (f : ℕ → M) :
    (μ.parts.map f).prod = (toExponents μ).prod (fun i k => f i ^ k) := by
  classical
  rw [← map_positiveParts μ, ← toMultiset_toExponents μ, Multiset.map_map,
    Finsupp.toMultiset_map, Finsupp.prod_toMultiset]
  exact Finsupp.prod_mapDomain_index (fun b => pow_zero b) (fun b m n => pow_add b m n)

@[simp] theorem toExponents_zero (μ : Nat.Partition 0) : toExponents μ = 0 := by
  ext i
  simp

@[simp] theorem prod_parts_zero {M : Type*} [CommMonoid M]
    (μ : Nat.Partition 0) (f : ℕ → M) : (μ.parts.map f).prod = 1 := by
  simp

end SymmetricFunctions.Partition
