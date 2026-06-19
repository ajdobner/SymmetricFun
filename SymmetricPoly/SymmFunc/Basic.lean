import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Combinatorics.Enumerative.Partition.Basic

namespace Nat.Partition

def parts_PNat (μ : Nat.Partition n) : Multiset ℕ+ :=
  μ.parts.pmap (fun i hi => ⟨i, hi⟩) (fun _ hi => μ.parts_pos hi)

def toFinsupp (μ : Nat.Partition n) : ℕ+ →₀ ℕ :=
  sorry

def union (μ : Nat.Partition m) (ν : Nat.Partition n) : Nat.Partition (m + n) :=
  Nat.Partition.mk (μ.parts + ν.parts)
    (by
      intro i hi
      rw [Multiset.mem_add] at hi
      cases hi
      case inl hl => exact μ.parts_pos hl
      case inr hr => exact ν.parts_pos hr)
    (by
      rw [Multiset.sum_add, μ.parts_sum, ν.parts_sum]
    )

end Nat.Partition


namespace MvPolynomial

noncomputable def WeightedHomogeneousSubmodule.basisMonomials (σ : Type*) (R : Type*)
    [CommSemiring R] [AddCommMonoid M] (w : σ → M) (n : M) :
    Module.Basis {m : σ →₀ ℕ // m.weight w = n} R (weightedHomogeneousSubmodule R w n)  :=
  Module.Basis.ofRepr (
    (LinearEquiv.ofEq _ _ (weightedHomogeneousSubmodule_eq_finsupp_supported R w n)).trans
    (Finsupp.supportedEquivFinsupp {m : σ →₀ ℕ | m.weight w = n})
  )

end MvPolynomial

-- Define it as a structure to completely seal off the definition
abbrev SymmFunc (R : Type*) [CommSemiring R] := MvPolynomial ℕ+ R

namespace SymmFunc
variable {R : Type*} [CommSemiring R]

def IsHomogeneous (f : SymmFunc R) (n : ℕ) : Prop :=
  MvPolynomial.IsWeightedHomogeneous (fun (i : ℕ+) => (i : ℕ)) f n

def homogeneousSubmodule (R : Type*) [CommSemiring R] (n : ℕ) : Submodule R (SymmFunc R) :=
  MvPolynomial.weightedHomogeneousSubmodule R (fun (i : ℕ+) => (i : ℕ)) n

theorem HomogeneousSubmodule.gradedMonoid :
  SetLike.GradedMonoid (homogeneousSubmodule R) :=
    MvPolynomial.WeightedHomogeneousSubmodule.gradedMonoid

noncomputable instance : GradedAlgebra (homogeneousSubmodule R) :=
  MvPolynomial.weightedGradedAlgebra R (fun (i : ℕ+) => (i : ℕ))

noncomputable def e (k : ℕ) : SymmFunc R :=
  match k with
  | 0 => 1
  | k + 1 => MvPolynomial.X ⟨k + 1, Nat.succ_pos k⟩

noncomputable def ePart (μ : Nat.Partition n) : SymmFunc R := (μ.parts.map e).prod

noncomputable def HomogeneousSubmodule.eBasis (n : ℕ) :
    Module.Basis (Nat.Partition n) R (homogeneousSubmodule R n) := sorry
  -- MvPolynomial.WeightedHomogeneousSubmodule.basisMonomials ℕ+ R (fun (i : ℕ+) => (i : ℕ)) n

end SymmFunc
