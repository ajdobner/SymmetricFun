import SymmetricFunctions.Basic
import SymmetricFunctions.Partition
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Data.ZMod.Basic

/-!
# Foundation conventions

These examples exercise zero coefficients, torsion-valued algebra evaluation,
and repeated and empty partitions. They assert no lambda structure on the target.
-/

namespace SymmetricFunctions.Examples

noncomputable section

open SymmetricFunction Partition

-- All examples must elaborate with the representation sealed.
attribute [local irreducible] SymmetricFunction

example {R : Type*} [CommSemiring R] (S : Subalgebra R (SymmetricFunction R))
    (h : ∀ i : ℕ+, e (i : ℕ) ∈ S) (f : SymmetricFunction R) : f ∈ S := by
  induction f using SymmetricFunction.induction_on with
  | C r => exact S.algebraMap_mem r
  | add f g hf hg => exact S.add_mem hf hg
  | mul_e f i hf => exact S.mul_mem hf (h i)

example : e (R := PUnit) 7 = 0 := by
  apply (polynomialEquiv PUnit).injective
  exact Subsingleton.elim _ _

example (x : ℕ+ → ZMod 4) :
    eval (R := ℤ) x (4 * e 1 + e 2) = x 2 := by
  simp only [map_add, map_mul, map_ofNat, eval_e_succ]
  rw [show (4 : ZMod 4) = 0 from ZMod.natCast_self 4]
  simp

private def twoTwoOne : Nat.Partition 5 :=
  Nat.Partition.ofSums 5 {2, 2, 1} (by decide)

example : toExponents twoTwoOne 2 = 2 := by
  simp [twoTwoOne, Nat.Partition.ofSums]

example : toExponents twoTwoOne 3 = 0 := by
  simp [twoTwoOne, Nat.Partition.ofSums]

example : (toExponents twoTwoOne).weight (fun i : ℕ+ => (i : ℕ)) = 5 :=
  finsupp_weight_toExponents twoTwoOne

example (R : Type*) [CommRing R] :
    (toExponents twoTwoOne).prod (fun i k => e (R := R) i ^ k) = e 2 ^ 2 * e 1 := by
  rw [← prod_parts]
  simp [twoTwoOne, Nat.Partition.ofSums, Multiset.filter_singleton, pow_two, mul_assoc]

example : exponentEquiv 0 (default : Nat.Partition 0) = ⟨0, by simp⟩ := by
  apply Subtype.ext
  exact toExponents_zero _

example (R : Type*) [CommRing R] :
    ((default : Nat.Partition 0).parts.map (e (R := R))).prod = 1 :=
  prod_parts_zero _ _

end

end SymmetricFunctions.Examples
