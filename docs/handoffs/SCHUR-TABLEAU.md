# Tableau identification of the existing Schur functions

- Task SCHUR-TABLEAU; owner Codex (single worker); status in_progress.
- Base d276255; original acceptance criteria retained verbatim in tasks.json.
- Dependencies: SCHUR-JT and TABLEAU-FINITE; latter is being implemented first.
- Environment pins unchanged; no reference code copied.

## Proposed contract and statement review

For arbitrary CommRing R, ξ : Nat.Partition d and every N : Nat,
`alphabetSpecialization R (Fin N) (schur ξ) =
 Partition.FiniteTableau.generatingPolynomial ξ N R`.
The left side is the existing Jacobi–Trudi determinant, unchanged. The right
side is a genuine sum over bounded Mathlib tableaux. There is no length≤N
hypothesis and no rational or Nontrivial assumption. Coefficients are natural
fixed-content counts cast into R. Derive zero-last-variable compatibility and
vanishing when length ξ > N. A generating-polynomial definition by itself
does not prove this contract.

## Reuse search and intended proof route

Pinned Mathlib has YoungDiagram, SemistandardYoungTableau, finite determinants,
and finite sums, but no Schur/tableau identity or skew tableau adapter was
found (local declaration search plus source search on 2026-10-16).
Use branching, sharing the infrastructure with skew tableaux:
1. Define horizontal strips by containment and row interlacing
   λ_(i+1) ≤ μ_i ≤ λ_i, and prove the equivalent at-most-one-cell-per-column fact.
2. Prove one-variable specialization of the existing skew determinant equals
   x^(|λ|-|μ|) for a horizontal strip and zero otherwise. This is an integral
   determinant calculation, including all boundary cases.
3. Prove the skew coproduct composition law from the existing Hall adjunction
   and Schur orthonormality. This supplies the algebraic branching identity.
4. Prove the actual tableau bijection removing the largest letter; its removed
   cells form a horizontal strip and the contents split as expected.
5. Induct on alphabet size, using the explicit branching identities.
All these are proof obligations, not assumed lemmas. The common skew proof may
be developed before the straight specialization corollary if that simplifies
interfaces; task dependency/status updates must describe that accurately.

## Remaining obligations

All of the identification above is open. TABLEAU-FINITE is the first checkpoint.
SKEW-TABLEAU and KOSTKA are separately registered and not claimed complete.
