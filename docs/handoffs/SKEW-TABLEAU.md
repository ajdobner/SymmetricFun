# Skew tableaux and their Schur identification

- Task SKEW-TABLEAU; owner Codex (single worker); status done.
- Base 612b93c; TABLEAU-FINITE and SCHUR-SKEW complete; pins unchanged.
- Scope Tableaux/Skew, Tableaux/SkewBranching, Schur/SkewTableaux and examples.
- No skew tableau API was found in pinned Mathlib; use a small finite-cell
  adapter, keeping Mathlib diagrams, partitions, and the straight tableau type.

## Proposed definitions and pre-proof statement review

`SkewTableau ξ μ N` has a proof field `contained : Contained μ ξ` and a filling
of `(ofPartition ξ).cells \ (ofPartition μ).cells` by Fin N. Weak row comparisons
and strict column comparisons quantify over two cells of that difference only.
The proof field makes the type empty if containment fails. Its presence is
proof-irrelevant and does not duplicate a tableau. Entries are not forced to
extend a straight filling and are never compared with zeros in missing cells.
Finiteness is proved through the actual finite function space. Content is the
sum of singleton multiplicities; its degree is d-e by finite set difference
cardinality and explicit containment. Define weights, natural counts, and finite
weight sums independently of R. Equal shapes have one empty filling even when
N=0. With empty inner shape prove an actual equivalence to Partition.FiniteTableau,
with matching contents, weights, and sums.

The later theorem, still open, is for every CommRing R and all ξ,μ,N:
`alphabetSpecialization R (Fin N) (skewSchur ξ μ) =
 SkewTableau.generatingPolynomial ξ μ N R`.
No containment assumption is needed in this final equality because both sides
are zero for noncontainment; the filling structure itself carries containment.
This is the existing Hall-adjoint skew Schur with its proved skew determinant.
The shared horizontal-strip branching route is recorded in SCHUR-TABLEAU.md.

Statement review: membership of both compared cells is explicit. Thus a hole
never forces a comparison with a fabricated entry. A noncontained pair has no
objects even if its raw set difference is empty. This faithfully models zero,
whereas equal contained shapes have one empty object and polynomial one.
These conventions are combinatorial infrastructure, not the Schur identity.

## Remaining obligations

Implement and validate the finite adapter, straight equivalence and boundary
examples first. Then prove branching/bijections and the general skew Schur formula.

## Horizontal-strip base case: proposed declarations and review

`HorizontalStrip μ ξ := Contained μ ξ ∧ ∀ i, rowLength ξ (i+1) ≤ rowLength μ i`.
Prove this is equivalent to at most one difference cell in each column.
`SkewTableau.nonempty_one_iff : Nonempty (SkewTableau ξ μ 1) ↔ HorizontalStrip μ ξ`.
All one-letter fillings are equal; when a horizontal strip exists its polynomial
is `X 0 ^ (d-e)`, otherwise zero. This includes equal shapes and the empty shape.
The exponent d-e uses containment, so it represents the actual number of cells;
it is not the truncation of an unsupported negative degree. These are statements
about actual tableaux and do not assume a one-variable skew Schur formula.
Module Partition/HorizontalStrip.lean owns the row/cell equivalence.

## Finite adapter checkpoint (2026-10-17)

The finite adapter and every boundary/base-case declaration above are proved.
`straightEquiv` is a two-sided equivalence, not merely an injection; its contents
agree, so the empty-inner generating polynomial is the straight weight sum.
The row/cell horizontal-strip equivalence and genuine one-letter generating
polynomial are proved, including equal and noncontained shapes. Examples include
(2,1)/(1) filled entirely with 0, which need not extend to a straight tableau,
and a noncontained inner column inside a longer outer row.

Independent review of scripts/ReviewTableaux.lean confirms actual difference
cells, proof-irrelevant containment, comparisons between present cells only,
correct d-e content size, and no claimed connection to skewSchur yet.
Lean MCP reports no diagnostics for Tableaux/Skew. Full check_project.py passed:
134 accepted modules and 2,332 transitive axiom audits; only propext,
Classical.choice and Quot.sound. All five checker tests passed. Declaration
and statement-review scripts passed after the root build. The first attempted
review ran before the rebuilt root object existed; it was rerun after the build,
not treated as a successful check. Logs: /tmp/skew-tableau-finite-check.log and
/tmp/skew-tableau-finite-review.log. Pins and reference checkouts are unchanged.

Exact source SHA-256:
- Partition/HorizontalStrip.lean: 436061bd48e08ba63f52db0770dabbd8267f79c1fb8089a26bd6747e6c2cae4b
- Tableaux/Skew.lean: 70cfb664a948f47f993815d82d48f59d3452f9e4b869aac6d45512dcae57bb6a
- Examples/SkewTableaux.lean: fbbb6f328af2a29148eaadddead4b4828d70df9f1b608df5d29fcfdddb2c8d80

SKEW-TABLEAU remains in_progress. Next: prove one-letter specialization of the
existing skew determinant, then algebraic and actual-tableau branching. The
full straight/skew Schur identifications and Kostka theory are still open.

## Largest-letter bijection: precise next interfaces (2026-10-17)

For T : SkewTableau ξ μ (N+1), let `lowerDiagram T` consist of all μ cells
and the actual skew cells whose entry is <N. Prove it is a lower set using
row/column monotonicity between present cells, and hence a genuine Mathlib
YoungDiagram. It lies between μ and ξ. Convert it using `YoungDiagram.toPartition`
to `lowerShape T : Σ n : Fin(d+1), Nat.Partition n`; no replacement partition is used.
The removed difference has at most one cell per column, since removed entries
are all N. `removeLargest T : SkewTableau (lowerShape T).2 μ N` restricts entries.
Conversely, `extendLargest` takes a tableau U of shape ν/μ and a proof of
HorizontalStrip ν ξ, keeps its entries and places N in ξ/ν. Prove its weak-row
and strict-column conditions on present cells. These are inverse constructions,
including empty alphabets and noncontained pairs.

The weight identity is `weight (extendLargest U hs) =
 rename Fin.castSucc (weight U) * X (Fin.last N)^(d-n)`.
It follows by partitioning the finite actual cell set into ν/μ and ξ/ν,
not by an assumed branching identity. Summation along the proved bijection
must yield the same finite branching formula as alphabetSpecialization.
These proofs remain open until their actual Lean declarations are validated.

## Completion (2026-10-17)

SKEW-TABLEAU is done. The finite cell adapter, explicit containment field,
correct row/column comparisons, empty-inner equivalence, equal-shape uniqueness,
noncontainment zero, actual largest-letter bijection and weight factorization
are all proved. `alphabetSpecialization_skewSchur_eq_tableaux` identifies the
EXISTING Hall-adjoint skew function, already proved equal to the skew determinant,
with its actual weight sum for every finite alphabet over every CommRing.
`coeff_alphabetSpecialization_skewSchur` gives natural counts; integer monomial
coefficients are nonnegative. No Schur positivity or LR conclusion is claimed.

The complete acceptance/independent statement review, exact source hashes,
all-module validation (140 modules and 2,433 transitive axiom audits), five
checker tests, diagnostics and examples are recorded in SCHUR-TABLEAU.md's
completion entry. Both tasks share that checked source state based on 3781965.
The full objective still requires KOSTKA; proceed without waiting for confirmation.
