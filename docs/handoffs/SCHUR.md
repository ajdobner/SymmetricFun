# Schur, Hall, skew and Cauchy theory

- Parent SCHUR; owner Codex (single worker); status in_progress.
- Base 9f0eaee: 89 modules, 1,652 audited declarations; SERIES/COMPLETION done.
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612; pins unchanged.
- Module ownership/dependencies and all acceptance criteria are in tasks.json.
- Reference checkouts remain read-only; no new colleague code is copied.

## Decomposition and proposed mathematical interfaces

The original three parent acceptance criteria are preserved verbatim. Nine required
subtasks make the user's full contract explicit; SCHUR-TABLEAU separately tracks
an unproved future combinatorial identification and is not a parent prerequisite.

For λ : Nat.Partition d, rowLength λ i is YoungDiagram.ofPartition λ's existing
rowLen i. Its number of nonzero rows is λ.parts.card. Containment μ⊆λ means
YoungDiagram.ofPartition μ ≤ YoungDiagram.ofPartition λ, allowing different sizes.
Conjugation is exactly Nat.Partition.conjugate. The future tableau source is
SemistandardYoungTableau (YoungDiagram.ofPartition λ), with finite-alphabet entry
bounds on cells; no alternate tableau or partition structure is introduced.

For CommRing R, completeInt k equals h k.toNat when 0≤k and zero otherwise.
The matrix at size L is h_{(rowLength λ i : ℤ)-(i : ℤ)+(j : ℤ)}, i,j : Fin L.
`schur λ` is its determinant at the number of rows. The padding theorem equates
it to every L at least that length. Finite specialization is the determinant of
finite hsymm with the same integer convention, not a claimed tableau formula.

SCHUR-BASIS must prove an integral triangular transition of this actual determinant
family to the complete basis, with diagonal one, then homogeneous/full bases over
arbitrary rings. SCHUR-DUAL proves the elementary determinant for the conjugate
shape and omega(schur λ)=schur λ.conjugate. Both retain all zero-index conventions.

`hall : SF R →ₗ[R] SF R →ₗ[R] R` will have hall(hPart λ,mPart μ)=δ_λμ
(with sigma partition indexing across degrees). Symmetry, separate nondegeneracy,
and degreewise perfectness are required, plus Schur orthonormality for the actual
Schur basis. `tensorHall` must satisfy tensorHall(f⊗g,u⊗v)=hall(f,u)*hall(g,v).
The Hopf adjunction is hall(f*g,h)=tensorHall(f⊗g,Δh).

`skewing f : SF R →ₗ[R] SF R` must satisfy hall(skewing f g,h)=hall(g,f*h).
For homogeneous f,g of sizes a,b, it vanishes if b<a and otherwise has degree b-a.
`skewSchur λ μ := skewing (schur μ) (schur λ)` must equal the determinant
h_{λ_i-μ_j-i+j}, with all casts before subtraction, at every sufficient common
padding. Prove empty/equal/noncontained shapes and Δs_λ=∑μ s_{λ/μ}⊗s_μ.

`cauchyKernel : CompletedTensor R` has degree-2d component ∑λ:Partition d s_λ⊗s_λ
and zero odd components. Prove the same components are ∑λ h_λ⊗m_λ. A new completed
tensor specialization sends it to the finite product of actual formal-series
units (1-X(inl i)*X(inr j))⁻¹. Total degree counts both alphabets. This is the
product alphabet Cauchy kernel, not the completed coproduct of Omega. Any notation
must refer to these proved maps, with all finiteness/positive-order hypotheses.

## Pre-proof statement review

These are bounded Schur functions in the unchanged polynomial-backed ring.
The determinant, integral transition and Hall normalization are substantive proof
obligations, not definitions by relabeling or rational-basis descent. All general
results include torsion and zero rings. Perfectness is only degreewise; no full
algebraic-dual equivalence is proposed. Tableau formulas, positivity, LR theory,
flagged/LLT theory and publication remain outside the claimed work.

## Reuse search and validation

Pinned Mathlib supplies YoungDiagram.ofPartition/toPartition, partition conjugation,
rowLen and rowLens, and SemistandardYoungTableau. No Schur/Jacobi–Trudi library was
found in the pin. Reuse determinant, finite permutation, graded basis and tensor
APIs before adding infrastructure. Each implementation subtask records exact
interfaces, separate mathematical review, compiler/MCP checks, full integration,
checker tests and transitive axiom audit. No SCHUR result is yet claimed complete.

## Progress checkpoints

- 5a9ca9d: SCHUR-PART complete, existing Mathlib rows/containment/tableau adapters.
- b67fc85: SCHUR-JT complete, actual determinant, padding, degree, naturality,
  finite specialization, empty/row/column formulas.
- 4ba39c0: SCHUR-BASIS complete, integral unit-determinant transition and
  homogeneous/full graded Schur bases, including torsion and zero rings.
- SCHUR-DUAL checkpoint: complete dual determinant and omega/conjugation with
  explicit complementary-minor and boundary-sign proofs; see its source hashes.

HALL-CORE is complete: classical duality, symmetry by matrix transposition,
degreewise perfectness, and multiplication/coproduct adjunction (110 modules,
1,970 audited declarations). See HALL-CORE.md for exact source hashes.

HALL-SCHUR is complete: integral bialternants and alternating coefficient
extraction prove orthonormality for the existing Hall form (114 modules, 2,021
audited declarations). See HALL-SCHUR.md for exact checked source hashes.

The next task is SCHUR-SKEW. CAUCHY-FINITE and
SCHUR-CAUCHY remain open; the parent SCHUR goal is not complete. No tableau or
Littlewood–Richardson positivity claim is made.

SCHUR-SKEW first checkpoint: bounded adjoints, degree behavior, empty/equal
shapes and finite skew coproduct expansion accepted (117 modules, 2,057 axioms
checked). The general skew determinant and noncontained-shape vanishing remain
open; SCHUR-SKEW and parent SCHUR remain in_progress.

SCHUR-SKEW is now complete: the actual Hall-adjoint skew function equals every
sufficiently padded integer-index determinant, and YoungDiagram noncontainment
implies zero. Full checkpoint: 120 modules, 2,095 transitive axiom checks;
see SCHUR-SKEW.md for exact source hashes and independent statement review.
Next: CAUCHY-FINITE and SCHUR-CAUCHY; parent SCHUR remains in_progress.

CAUCHY-FINITE is complete: actual completed tensor specialization, formal inverse
product, coefficient formula, h/m even components and odd vanishing. Full audit:
126 modules and 2,158 transitive axioms; exact sources in CAUCHY-FINITE.md.
SCHUR-CAUCHY is now the final ready parent subtask.
