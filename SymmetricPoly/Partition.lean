import Mathlib.Data.List.Sort

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
def get (p : Partition) (i : ℕ) : ℕ := p.parts.getD i 0

/-- Number of parts (equals the number of nonzero entries). -/
def length (p : Partition) : ℕ := p.parts.length

/-- Total size (sum of all parts). -/
def size (p : Partition) : ℕ := p.parts.sum

/-- The empty partition. -/
def empty : Partition := ⟨[], List.Pairwise.nil, by simp⟩

/-- Componentwise order: μ ≤ ν iff every part of μ is ≤ the corresponding part of ν. -/
instance instLE : LE Partition := ⟨fun μ ν => ∀ i, μ.get i ≤ ν.get i⟩

instance instDecidableEq : DecidableEq Partition :=
  fun p q =>
    if h : p.parts = q.parts then isTrue (Partition.ext h)
    else isFalse (fun heq => h (congrArg Partition.parts heq))


def Interlaces (μ ν : Partition) : Prop :=
  ∀ i : ℕ, ν.get i ≥ μ.get i ∧ μ.get i ≥ ν.get (i + 1)

/-- Notation for interlacing partitions. -/
scoped infix:50 " ≺ " => Interlaces


/-- These declarations will be specific to the fusion ring context. -/
def IsNPartition (N : ℕ) (p : Partition) : Prop :=
  p.length ≤ N

def IsNLPartition (N L : ℕ) (p : Partition) : Prop :=
  p.length ≤ N ∧ p.get 0 ≤ p.get (N - 1) + L

end Partition
