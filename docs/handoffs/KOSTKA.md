# Natural Kostka coefficients

- Task KOSTKA; owner Codex (single worker); status done.
- Base 27bdf1b; SCHUR-TABLEAU and MONOMIAL complete; pins unchanged.
- Scope Tableaux/Kostka.lean, Schur/Kostka.lean, Examples/Kostka.lean.
- Pinned Mathlib source search found no partition dominance or Kostka API.
  Reuse the established finite tableaux, actual monomial basis, exponent orbit
  classification, finite sums, and Mathlib partitions.

## Precise proposed declarations and pre-proof review

`Partition.rowContent μ N : Fin N →₀ Nat` has coordinate i equal to rowLength μ i.
For N≥length μ, prove its exponent multiset is exactly μ.parts and its degree
is |μ|. `FiniteTableau.content_highestWeight` identifies the content of the
existing highest-weight tableau with rowContent. For ξ,μ : Nat.Partition d,
`kostka ξ μ : Nat := FiniteTableau.contentCount ξ (rowContent μ d)`.
This definition is a genuine finite natural count and is independent of R.
Alphabet-padding independence says every N≥length μ gives the same count,
including N=0 in degree zero. Use the proved coefficient identity and the
monomial basis's representative/alphabet independence over ℤ, then natural-cast
injectivity; no counting over a torsion ring is used to infer equality in Nat.

For every CommRing R, prove `schur ξ = ∑ μ : Nat.Partition d,
 (kostka ξ μ : R) • mPart μ`. The actual m basis has coefficient one at each
exponent of shape μ. Thus K counts one fixed content, with no extra permutation
or repeated-part factorial. Prove the actual basis coordinates equal K.

`Dominates ξ μ := ∀ k, (∑ i ∈ range k, rowLength μ i) ≤
 (∑ i ∈ range k, rowLength ξ i)` fixes the direction: the Schur shape ξ
must dominate the content partition μ. For every tableau, entries are at least
their row number. Hence letters <k occur only in rows <k; prove the prefix
cardinality inequality and derive zero counts when dominance fails.
For diagonal content prove the highest-weight filling is unique, using the
entry≥row inequalities and equality of their finite weighted sums. Conclude
`kostka ξ ξ = 1`, including the empty shape. Nonnegativity is a Nat/Int statement.

Review: no rational descent, no Nontrivial assumption, no identification of
all orbit permutations as separate monomial coefficients. The dominance
inequality is explicit, not a reversed unnamed order. A one-letter or a
small-shape example does not replace general diagonal/vanishing proofs.
Include (2,1) coefficient/count two at x1*x2*x3, repeated entries, rows/columns,
empty alphabets and shapes, and casts to a torsion ring. LR and arbitrary skew
Schur positivity are outside the claim.

## Elaborated interface and separate statement review (2026-10-17)

The proposed interfaces above are now proved with the exact declarations:

- Partition.rowContent, rowContent_apply, rowContent_embDomain,
  exponentParts_rowContent, degree_rowContent, weight_rowContent_prefix.
- Partition.FiniteTableau.content_highestWeight, weight_content,
  eq_highestWeight_of_content, contentCount_diagonal, dominates_of_content.
- Partition.kostka, Dominates, kostka_self, kostka_eq_zero_of_not_dominates.
- SymmetricFunction.mBasis_repr_schur, contentCount_rowContent,
  coeff_schur_eq_kostka, contentCount_eq_kostka,
  schur_eq_sum_kostka_mPart, mBasis_repr_schur_nonneg.

Single-worker statement review: scripts/ReviewTableaux.lean prints the actual
rowContent/kostka/Dominates definitions and the elaborated theorem statements,
separately from proof compilation. The printed hypotheses confirm:

1. Kostka is the cardinality of actual finite Mathlib tableaux with one content,
   independent of any ring. The size-d alphabet always suffices for μ because
   every positive part contributes at least one to d. Empty degree uses Fin 0.
2. Padding needs only N≥length μ, not N≥length ξ. If the shape has too many
   rows, the existing tableau type is empty and the resulting count is zero.
   The more general exponent-orbit theorem has only exponentParts a=μ.parts.
3. The full expansion refers to the original determinant schur and existing
   stable mPart. It assumes only CommRing R; no domain, Nontrivial, characteristic
   zero, rationality or special lambda structure has been introduced.
4. Diagonal one is proved by actual uniqueness: the sum of numerical entries
   is fixed by content, while every entry is at least its row index. Equality
   of sums makes each entry its row index. The proof covers degree zero.
5. Dominance is explicitly forall k, prefix(μ,k)≤prefix(ξ,k). Counting letters
   less than k gives a subset of the first k rows. No dominance order is reversed,
   and vanishing is proved for the natural count rather than a possibly
   noninjective cast into a torsion ring.
6. Positivity is integer monomial-coefficient nonnegativity. No LR coefficient,
   skew Schur-basis positivity, or unrestricted infinite operation is asserted.

Proof architecture: partition rows classify their exponent orbit; the existing
Schur tableau coefficient theorem and mBasis_repr_eq_coeff identify coordinates.
Only equality of natural counts uses ℕ→ℤ injectivity. The expansion uses basis
reconstruction over the actual coefficient ring, without descent from ℚ.

Examples/Kostka verifies empty shape and alphabet, a row with three repeated
letters, column/row dominance failure, alphabet size seven, torsion coefficients,
coefficient one for repeated content (2,1,0), and coefficient/count/Kostka number
two for shape (2,1) and content (1,1,1). The numerical value is derived from the
actual 2x2 Jacobi–Trudi determinant h2*h1-h3 and complete-polynomial coefficients,
then transported to the finite count by the proved tableau identity.

Useful engineering detail: the pinned AddMonoidAlgebra.coeff_add returns an
equality of Finsupps; use Finsupp.add_apply before coefficient multiplication
lemmas. Fin.sum_univ_eq_sum_range needs an explicit function when an if-expression
contains multiple occurrences of the coerced Fin index. No mathematical
obstruction or contract change was needed. No copied colleague code, uploads,
or changes to pins/reference repositories were made.

## Validation and completed source state

Base checkpoint 27bdf1b plus the files below. Lean v4.34.1 and Mathlib
 d13f23b723b8a846827a245b89c10fc7d3f11612 remain pinned.

- `lake build SymmetricFunctions`: exit 0, all affected dependents built.
- `python3 scripts/check_project.py`: exit 0; 49 registry tasks,
  143 accepted modules, 2,478 declarations audited transitively. The final
  run has no warnings. Only propext, Classical.choice and Quot.sound occur.
  Root import coverage includes all three new modules.
- `python3 scripts/test_check_project.py`: exit 0, all five tests pass.
- `lake env lean scripts/ReviewTableaux.lean`: elaborated definitions,
  assumptions and representative axiom dependencies reviewed separately.
- `lake env lean scripts/DeclarationIndex.lean`: exit 0, 1,753 noninternal
  accepted declarations indexed; private helpers and anonymous examples are
  additionally included in the full transitive audit.
- Lean MCP diagnostics: no errors or warnings in all three new modules.
- Logs: /tmp/kostka-check.log and /tmp/kostka-review.log. These are convenience
  logs; the committed source and commands above are the reproducible evidence.

Exact source SHA-256:
- Tableaux/Kostka.lean: f5ba192128f79ded6d2ef7fdaef3176e95bc6c85c91a2f1f43aceb153eac8568
- Schur/Kostka.lean: b9d285e7f157fd6b417ff3f95288e3c53b52a175bf6466ed07ea009dbb37cc3f
- Examples/Kostka.lean: a3ba080295bf23acb7fe9658bf61728b96a428395be4366451ac5eb900454b98
- SymmetricFunctions.lean: bb12535d6f10628ec1c06f454d3be37454aa34964107cba660c7137feb0e3c64
- scripts/ReviewTableaux.lean: 0358d35cb08a7d676221b504a6dec2dad45c1ebf685f1876b5712f64ae6c90b4

All KOSTKA acceptance criteria are satisfied. Together with TABLEAU-FINITE,
SCHUR-TABLEAU and SKEW-TABLEAU at their preceding checkpoints, this completes
this run's tableau-and-natural-coefficient goal. There are no outstanding
proof goals in these tasks. The polynomial foundation and weighted degree
are preserved. Littlewood–Richardson theory, flagged/LLT results, optional
external tooling and publication remain outside this completed goal.
