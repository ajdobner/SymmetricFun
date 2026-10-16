# Finite tableaux, content and weights

- Task TABLEAU-FINITE; owner Codex (single worker); status done.
- Base d276255; SCHUR-PART complete. Lean 4.34.1 and Mathlib
  d13f23b723b8a846827a245b89c10fc7d3f11612 unchanged.
- Scope Tableaux/Basic.lean and Examples/Tableaux.lean.
- Mathlib's Jake Levinson SemistandardYoungTableau and YoungDiagram are reused
  by import. No reference source is copied; reference checkouts stay unchanged.

## Proposed precise interfaces and pre-proof statement review

For ξ : Nat.Partition d and N : Nat, retain Partition.FiniteTableau ξ N exactly.
`FiniteTableau.filling T : {c // c ∈ (YoungDiagram.ofPartition ξ).cells} → Fin N`
is the actual cell entry. Prove injectivity, then use the finite filling space
for the Fintype instance. No infinite set of functions is asserted finite.
`FiniteTableau.content T : Fin N →₀ Nat` counts cells with each entry.
`content_apply` identifies it with a finite fiber cardinality;
`degree_content T : (content T).degree = d` counts each cell once.
`weight (R) T := MvPolynomial.monomial (content T) 1`.
`generatingPolynomial ξ N R := ∑ T : FiniteTableau ξ N, weight R T`.
`contentCount ξ a : Nat` counts tableaux with the specified exponent a.
The coefficient of the generating polynomial is exactly this count cast into R.
Coefficient change commutes with weight and generatingPolynomial for every
CommRing, including the zero ring. Empty shapes have exactly one tableau with
zero content and weight one, for every N including zero. Nonempty shapes have
no tableaux over Fin 0. More generally length ξ > N implies no tableaux,
because every entry in row i is at least i.

Statement review (separate from proof): alphabet bound applies only on actual
cells; zeros outside the diagram are ignored by content. Finiteness and counts
are independent of R. The generating polynomial is not yet identified with
Schur. Mathlib entry k means paper letter k+1 and variable x_(k+1); mathematical
row zero is the longest row. It is drawn at the bottom in French convention,
so the same increasing row index moves upward in the paper, downward in
Mathlib's English-style diagram. No transpose/conjugation is implied.

## Validation

Pending implementation, compiler diagnostics, independent printed-statement
review, all-module integration and transitive axiom checks. No completion claim.

## Accepted implementation and independent statement review

All proposed interfaces above are proved. The weight and coefficient-map API
needs only CommSemiring, a conservative generalization that includes ℕ and all
promised commutative rings. `highestWeight` is the bounded existing Mathlib
highest-weight tableau; `nonempty_iff` proves the row obstruction is exact.
`weight_eq_prod` independently checks the cell-count interpretation, and both
weights and their sum are homogeneous of alphabet degree d. No determinant
identification is hidden in a definition or assumed instance.

The printed definitions/hypotheses in scripts/ReviewTableaux.lean were reviewed
separately: actual cells only, a genuine finite enumeration, fixed-content counts,
proof-irrelevant bounds, and empty/zero-alphabet behavior all match the contract.
Examples check repeated letters in a row, the strict-column obstruction, count
nonnegativity over ℤ, coefficient casts to ZMod 6, and the zero coefficient ring.

Validation: `lake build SymmetricFunctions.Tableaux.Basic
SymmetricFunctions.Examples.Tableaux` passed without warnings; Lean MCP diagnostics
for Basic returned no messages. `scripts/check_project.py` passed with 131 accepted
modules and 2,226 transitive declaration audits (only propext, Classical.choice,
Quot.sound); five `scripts/test_check_project.py` tests passed. The statement
review and DeclarationIndex scripts passed, indexing 1,603 noninternal declarations.
The final repeat is logged at /tmp/tableau-finite-check-final.log; original full
check and statement review are /tmp/tableau-finite-check.log and
/tmp/tableau-finite-review.log. Every accepted module is root-imported.

Exact source SHA-256:
- Tableaux/Basic.lean: 97776c1bcbf713aac2e8a52e2d7ca49f369109985cb37bc377162bea457c8ef4
- Examples/Tableaux.lean: 968d0f90ee1d44888218f11a44085742e50156d0bff0f28fd2ca5f1949f92c47

Status done. No TABLEAU-FINITE criterion remains. SCHUR-TABLEAU, SKEW-TABLEAU,
and KOSTKA remain open. Next: finite skew adapters and horizontal-strip branching;
no tableau equality with Schur or Kostka dominance is claimed here.
