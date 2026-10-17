# Partition rows and Young diagram adapters

- Task SCHUR-PART; owner Codex (single worker); status done.
- Prerequisite PART complete; base 9f0eaee; pinned environment unchanged.
- Scope SymmetricFunctions/Partition/YoungDiagram.lean.

## Proposed precise declarations and statement review

For λ : Nat.Partition d define rowLength λ i := (YoungDiagram.ofPartition λ).rowLen i,
with length λ := λ.parts.card. Prove Antitone (rowLength λ), rowLength λ i=0 when
length λ≤i, and ∑i<L rowLength λ i=d whenever length λ≤L. Relate rows to the sorted
parts using Mathlib rowLens_ofPartition_eq_sort_parts and get_rowLens.
Define Contains/Contained only as the existing YoungDiagram order, with a
pointwise-row-length equivalence, and show conjugation agrees with transpose
and exchanges rows and columns. No new partition or conjugation is defined.

The actual tableau interface remains SemistandardYoungTableau
(YoungDiagram.ofPartition λ). A finite alphabet bounds entries only on shape cells;
zeros outside shape are inherited from Mathlib. No tableau generating formula is
proved or claimed here; its separate registry task remains planned.

Review: rows are zero-based and decreasing, zero padding does not add positive
parts, containment can compare different sizes, and the empty diagram has all
rows zero. The forthcoming determinant casts row lengths and indices to integers
before subtraction. No coefficient ring occurs in these combinatorial adapters.

## Reuse and proof plan

Pinned Mathlib YoungDiagram rowLen_anti, mem_iff_lt_rowLen/colLen, length_rowLens,
rowLens_ofPartition_eq_sort_parts, sum_rowLens_eq_card, and conjugate_conjugate.
Use those APIs for all proofs, retaining their exact partition and conjugate types.

## Accepted implementation and separate statement review

The reviewed declarations above are proved. Additional public interfaces include
`rowLength_pos_iff`, `Contained.size_le`, `ext_rowLength`, `length_conjugate`,
`contained_conjugate_iff`, `rowLength_indiscrete`, and
`rowLength_indiscrete_conjugate`. The one-row formula includes size zero; the
column formula is 1 precisely below its height. No replacement partition,
conjugation, or tableau definition was introduced. The general column bridge
`rowLength_conjugate` is explicit, not a simp rule, so it cannot preempt the
public one-column simplification theorem.

`ReviewSchur.lean` printed and separately reviewed the actual definitions,
padding bound, cross-size containment, and conjugation equations. They match
these contracts. Tableau enumeration/identification remains SCHUR-TABLEAU.

## Validation and exact source state

Base 9f0eaee plus this checkpoint:
- YoungDiagram.lean SHA256 89f1f6129a2538299ad7820cffb4beec9e605806b1278f943f851c6a1c829a78.
- Examples/PartitionRows.lean SHA256 06a184d9c24f71792cdd0f99a7a68f6bee23350adc6294c07177f1ed5294c4b1.
- `python3 scripts/check_project.py`: exit 0; 91 accepted modules, all 1,694
  declarations audited transitively; notation and lambda regressions pass.
- `python3 scripts/test_check_project.py`: exit 0, all five guard tests pass.
- `lake env lean scripts/ReviewSchur.lean`: exit 0; only the standard approved
  propext/Classical.choice/Quot.sound axioms.
- Lean MCP diagnostics for the examples: success, no errors or warnings.

Useful proof detail: prove a concrete sorted-parts equality first, then apply the
public row accessor theorem; rewriting inside dependent list indices directly
can trigger transparency errors. Multiset.filter_singleton is needed explicitly
in the small (2,1) computation. No remaining SCHUR-PART obligations.

Next: SCHUR-JT, as specified in its pre-proof handoff. Parent SCHUR remains open.
