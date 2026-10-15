# Partitions and weighted exponent vectors

- Task ID and owner: PART; Codex (single worker).
- Status: done.
- Prerequisite: ENV, checked at `f3439ea1033df550ce26723b1ff895ccad4b36a8`.
- Environment: Lean `v4.34.1`; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, unchanged.
- Implementation: `SymmetricFunctions/Partition.lean`.
- Supporting files: `SymmetricFunctions/Examples/Foundation.lean`, root imports,
  and task documentation, coordinated by the same worker as API.
- References: pinned Mathlib `Combinatorics/Enumerative/Partition/Basic.lean`,
  `Data/Finsupp/Multiset.lean`, and `Data/Finsupp/Weight.lean`.
  The colleague prototype proposes positive part multiplicities but leaves them
  unproved. This implementation uses Mathlib directly; no colleague replacement
  partition type or proof code is imported or copied.

## Mathematical contract

For every natural d, Mathlib's `Nat.Partition d` is equivalent to finitely
supported natural multiplicities on positive integers with weighted sum d.
The exponent at i is precisely the number of parts equal to i. The inverse
expands those multiplicities. Products indexed by parts agree with products of
powers indexed by the exponent support in every commutative monoid. Degree zero
corresponds to the empty multiset, zero exponent vector, and unit product.

## Formal interface

The pre-proof signatures were recorded here before implementation. The final
elaborated types were reviewed with `#check @...`. All names below live in
`SymmetricFunctions.Partition`, with `{d : ℕ}` implicit where applicable.

```lean
positiveParts (μ : Nat.Partition d) : Multiset ℕ+
toExponents (μ : Nat.Partition d) : ℕ+ →₀ ℕ
toExponents_apply (μ : Nat.Partition d) (i : ℕ+) :
  toExponents μ i = μ.parts.count (i : ℕ)
weight_toExponents (μ : Nat.Partition d) :
  ∑ i ∈ (toExponents μ).support, (i : ℕ) * toExponents μ i = d
ofExponents (a : ℕ+ →₀ ℕ)
  (ha : ∑ i ∈ a.support, (i : ℕ) * a i = d) : Nat.Partition d
ofExponents_toExponents (μ : Nat.Partition d) :
  ofExponents (toExponents μ) (weight_toExponents μ) = μ
toExponents_ofExponents (a : ℕ+ →₀ ℕ)
  (ha : ∑ i ∈ a.support, (i : ℕ) * a i = d) :
  toExponents (ofExponents a ha) = a
exponentEquiv (d : ℕ) : Nat.Partition d ≃
  {a : ℕ+ →₀ ℕ // ∑ i ∈ a.support, (i : ℕ) * a i = d}
weightedExponentEquiv (d : ℕ) : Nat.Partition d ≃
  {a : ℕ+ →₀ ℕ // a.weight (fun i : ℕ+ => (i : ℕ)) = d}
prod_parts {M : Type*} [CommMonoid M] (μ : Nat.Partition d) (f : ℕ → M) :
  (μ.parts.map f).prod = (toExponents μ).prod (fun i k => f i ^ k)
toExponents_zero (μ : Nat.Partition 0) : toExponents μ = 0
```

`positiveParts` lifts the existing parts through `Nat.toPNat`. `toExponents` uses
Mathlib's `Multiset.toFinsupp`. `ofExponents` maps `Finsupp.toMultiset` back to
natural numbers; no sorting or alternative partition representation is involved.

Additional exports are `map_positiveParts`, `toMultiset_toExponents`,
`sum_toMultiset`, `weight_eq_sum`, `finsupp_weight_toExponents`,
`ofExponents_parts`, `weightedExponentEquiv_apply`, `exponentEquiv_apply`,
`exponentEquiv_symm_apply`, and `prod_parts_zero`. Their exact signatures are in
the source identified below. `weightedExponentEquiv` is ready to index Mathlib's
weighted monomial basis in EBASIS.

## Statement review

The implementing worker performed a separate statement-only review after the
initial pre-proof review. No contract changes were needed. Mathlib's partition
excludes zero parts, so positive indices lose no information. Weighted sum is
`∑ i, i * multiplicity(i)`, not the number of parts. Mathlib's
`toFinsuppAntidiag` stores weighted values instead of multiplicities and therefore
is not substituted for this map. Both inverse laws quantify over every partition
or exponent vector of the stated size. `prod_parts` assumes only a commutative
monoid, and includes the empty product. There are no coefficient-ring or
additional finiteness hypotheses.

## Proof strategy and useful details

Lift parts to positive integers and use `Multiset.toFinsupp` and
`Finsupp.toMultiset`, with their inverse and counting laws. Calculate weighted
size by `Finsupp.sum_toMultiset` and `sum_mapDomain_index`. Restrict to the
specified size, and derive the product formula by `prod_toMultiset` and
`prod_mapDomain_index`. `weight_eq_sum` converts the natural scalar action in
`Finsupp.weight` to the registry's multiplication order.

A useful failed approach: directly returning `⟨i.val, proof⟩` from the multiset
map exposed the underlying subtype of the semireducible `PNat`. `rw
[Multiset.map_map]` then failed under implicit transparency with a codomain
mismatch `{n // 0 < n}` versus `ℕ+`. Using the typed constructor `Nat.toPNat`
fixes this without changing transparency options. Counting lemmas should receive
the explicit positive-to-natural map and `PNat.coe_injective`.

## Validation and integration

- Lean MCP searches, diagnostics, and goal inspection worked; final source and
  foundation examples have no errors or warnings.
- MCP `lean_verify` on `exponentEquiv`: only `propext`, `Classical.choice`,
  `Quot.sound`; no suspicious source patterns.
- `python3 scripts/check_project.py`: final run exited 0, built all five
  accepted modules without warnings, and audited the transitive axioms of all
  99 accepted declarations. Only the three allowed Lean foundations occur.
- `python3 scripts/test_check_project.py`: all five checker tests passed.
- `git diff --check`: passed.
- The partition `(2, 2, 1)` checks multiplicity two at index 2, zero at index 3,
  weight 5, and the elementary product `e 2 ^ 2 * e 1`. Empty-partition examples
  check the actual equivalence value is zero and the product is one.
- The exhaustive root imports include Partition and the examples. There are no
  imports of inherited `SymmetricPoly` drafts or replacement partition types.

## Checked source state and completion

SHA-256 source identifiers (before the final commit, independent of its hash):

| File | SHA-256 |
| --- | --- |
| `SymmetricFunctions/Partition.lean` | `5211fde55237d5333eebadc7688d70e2257a6bf056cf0ba81f32e7629e7920a9` |
| `SymmetricFunctions/Examples/Foundation.lean` | `5e6b9a6c5f0585b4c9d873e6fcc66b28d2cd3a6d781d71af87540556b9fddd32` |

All PART acceptance criteria, statement review, and integration checks passed
for the exact source hashes above.
There are no remaining PART proof obligations. EBASIS still waits for GRADE;
this equivalence alone is not a symmetric-function basis theorem.
