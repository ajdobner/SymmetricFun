import Mathlib.Data.List.Sort
import Mathlib.Data.PNat.Notation

/-! ## Partitions -/
/-- A partition: a weakly decreasing list of positive natural numbers,
    representing λ = (λ₁ ≥ λ₂ ≥ ... ≥ λ_k > 0). -/
@[ext]
structure Partition where
  parts : List ℕ
  sorted : List.Pairwise (· ≥ ·) parts
  pos : ∀ x ∈ parts, 0 < x

namespace Partition

/-- The i-th part (0-indexed), defaulting to 0. -/
def part (μ : Partition) (i : ℕ) : ℕ := μ.parts.getD i 0

/-- Number of parts (equals the number of nonzero entries). -/
def length (μ : Partition) : ℕ := μ.parts.length

/-- Total size (sum of all parts). -/
def size (μ : Partition) : ℕ := μ.parts.sum

macro:max atomic("|" noWs) μ:term noWs "|" : term => `(size $μ)

/-- The empty partition. -/
def empty : Partition := ⟨[], List.Pairwise.nil, by simp⟩

/-- Componentwise order: μ ≤ ν iff every part of μ is ≤ the corresponding part of ν. -/
instance instLE : LE Partition := ⟨fun μ ν => ∀ i, μ.part i ≤ ν.part i⟩

instance instDecidableEq : DecidableEq Partition :=
  fun μ ν =>
    if h : μ.parts = ν.parts then isTrue (Partition.ext h)
    else isFalse (fun heq => h (congrArg Partition.parts heq))


def Interlaces (μ ν : Partition) : Prop :=
  μ ≤ ν ∧ ∀ i : ℕ, μ.part i ≥ ν.part (i + 1)

def Cointerlaces (μ ν : Partition) : Prop :=
  μ ≤ ν ∧ ∀ i : ℕ, ν.part i ≤ (μ.part i) + 1

/-- Notation for interlacing partitions. -/
scoped infix:50 " ≺ " => Interlaces
scoped infix:50 " ≺' " => Cointerlaces

/-- These declarations will be specific to the fusion ring context. -/
def IsNPartition (N : PNat) (p : Partition) : Prop :=
  p.length ≤ N

def IsNLPartition (N L : PNat) (p : Partition) : Prop :=
  p.length ≤ N ∧ p.part 0 ≤ p.part (N - 1) + L

end Partition

open Partition

abbrev NLPartition (N L : PNat) := { p : Partition // IsNLPartition N L p }

namespace NLPartition

def getFirst (p : NLPartition N L) : ℕ := p.val.part 0
def getLast (p : NLPartition N L) : ℕ := p.val.part (N - 1)

def ofPartition {N L : PNat} (p : Partition) (h : IsNLPartition N L p) : NLPartition N L :=
  ⟨p, h⟩

end NLPartition
