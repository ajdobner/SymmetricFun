# Tableau identification of the existing Schur functions

- Task SCHUR-TABLEAU; owner Codex (single worker); status done.
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

## One-letter determinant: precise next declarations (2026-10-17)

For every CommRing R, define `oneLetterEvaluation R : SymmetricFunction R →ₐ[R] R`
as the actual finite one-letter specialization followed by evaluating its
variable at 1. Prove it takes every h_n to 1 and takes `completeInt k` to 1
if k≥0, else 0. Thus the padded skew determinant maps to the threshold matrix
`if (rowLength μ j : ℤ)-j ≤ (rowLength ξ i : ℤ)-i then 1 else 0`.
For HorizontalStrip μ ξ this matrix is upper triangular with diagonal one.
If containment holds but interlacing fails, choose the least failing row i;
rows i and i+1 of the matrix are equal. Noncontainment is already zero for the
actual skewSchur. Conclude the scalar is the horizontal-strip indicator.
Use the proved weighted homogeneity and actual finite specialization to recover
`alphabetSpecialization R (Fin 1) (skewSchur ξ μ) =
 if HorizontalStrip μ ξ then X 0 ^ (d-e) else 0`.

Review: evaluating at 1 is only applied to bounded polynomials; no completed
series is evaluated there. Homogeneity is the existing symmetric-function degree,
transported to total alphabet degree. No division, domain assumption or rational
coefficient argument is involved. The final exponent d-e describes a horizontal
strip only in the contained branch; the other branch is explicitly zero.

## Algebraic branching: proposed declarations and review

`comultiplication_skewing f g` identifies Δ(f-perp g) with
`TensorProduct.map LinearMap.id (skewing f) (Δ g)`. Prove it by the faithful
tensor Hall pairing and the existing multiplication adjunction. Then the
existing finite coproduct expansion gives
`Δ(skewSchur ξ μ) = ∑ n≤d, ∑ ν : Nat.Partition n,
 skewSchur ξ ν ⊗ skewSchur ν μ`.
No infinite sum or rational coefficients occur. Specializing the first factor
in the new last letter and the second in Fin N gives the successor-alphabet
branching sum, with coefficient X_last^(d-n) precisely when ν⊆ξ is horizontal.
All intermediate ν range over finitely many sizes ≤d; noncontained terms vanish.
The tableau deletion/extension bijection must still be proved independently.

## Algebraic branching checkpoint (2026-10-17)

The one-letter determinant and all algebraic branching declarations above are
proved. `alphabetSpecialization_one_skewSchur_eq_tableaux` now identifies the
actual Hall-adjoint skew function with the actual finite filling sum in one
letter, including noncontained shapes. The general formula is still open.
The threshold proof uses the first interlacing failure to obtain equal rows;
the positive case is upper triangular with diagonal one. Weighted homogeneity
recovers the polynomial after its bounded evaluation at one. The coproduct
branching proof uses the faithful tensor Hall pairing and finite algebraic
coproduct, without introducing a combinatorial assumption.

Independent printed-statement review confirms arbitrary CommRing (including
zero rings), correct integer determinant indices, finite intermediate sizes,
and Fin.castSucc/Fin.last alphabet conventions. The user-facing one-letter
formula is checked over ZMod 6 and PUnit, and row/column examples are included.
Lean MCP diagnostics for HorizontalStrip are empty. Full check_project.py passed
with 138 accepted modules and 2,361 transitive declaration audits (only propext,
Classical.choice and Quot.sound); all five checker tests passed. Review log:
/tmp/tableau-algebraic-branching-review.log. Full integration/axiom log:
/tmp/tableau-algebraic-branching-check.log. Declaration index regenerated.

Exact source SHA-256:
- Schur/HorizontalStrip.lean: c13a44cab6ce37ba7270442a575f69fbda139d7c604391e3df7a1b2b54974cb2
- Schur/Branching.lean: aae5973d72f354b08056d328c8856057ff817a186c03f3c32fec30e2461c4651
- Schur/SkewTableaux.lean: 3dd1df6524819f0b731ba1199ac1bd71267abf6fead081a8012f9375848fb1da
- Examples/TableauBranching.lean: 5514b88a9c95924899a7c9e513144376baee7caef9830677e45d2b5906bb612c

SCHUR-TABLEAU and SKEW-TABLEAU remain in_progress. Next: prove the actual
largest-letter deletion/extension bijection and its weight identity, then
induct on alphabet size. KOSTKA remains planned. Pins/reference checkouts
are unchanged, and no full tableau or Kostka theorem is claimed yet.

## Completion (2026-10-17)

SCHUR-TABLEAU is done. The original two acceptance criteria are preserved and
satisfied. `alphabetSpecialization_schur_eq_tableaux` identifies the EXISTING
Jacobi–Trudi determinant with weights of actual bounded Mathlib tableaux, for
every N and every CommRing. `rho_schur_eq_tableaux` supplies the symmetric-subalgebra
interface. `coeff_alphabetSpecialization_schur` is a fixed-content natural count;
`zeroLast_tableauGeneratingPolynomial` proves padding compatibility, and
`alphabetSpecialization_schur_eq_zero_of_length_gt` proves the small-alphabet
vanishing. No stable-range, rationality, domain or Nontrivial assumption appears.
The determinant and all foundational definitions remain unchanged.

Proof route completed: actual cell deletion/extension gives `branchingEquiv`;
`splitCellEquiv` proves the weight identity; finite summation gives combinatorial
branching. It matches the independently proved Hall/determinant algebraic
branching. The empty alphabet is handled by equal shapes, noncontainment and
positive homogeneous degree. Induction establishes the full skew formula, and
empty inner shape recovers the Mathlib straight tableau formula.

Separate statement review printed the actual shapes, deletion and extension,
BranchData, equivalence and final hypotheses in scripts/ReviewTableaux.lean.
There is no assumption of the desired identity and no renamed Schur basis.
Both directions of the bijection and the finite weight product are kernel checked.
Examples cover all alphabets, rows/columns, repeated entries, holes, noncontainment,
ZMod 6, and PUnit. The numerical (2,1) coefficient regression is reserved for
KOSTKA's explicitly retained acceptance criteria.

Validation: full check_project.py passed (140 modules, 2,433 transitive axiom
audits, only propext/Classical.choice/Quot.sound), all five checker tests passed,
Lean MCP diagnostics are clean, ReviewTableaux passed, and DeclarationIndex
indexed 1,731 noninternal declarations. Logs /tmp/tableau-formulas-check.log and
/tmp/tableau-formulas-review.log. An example initially lacked the Column import;
the targeted import was added and the complete validation rerun successfully.

Exact new/changed source SHA-256:
- Tableaux/SkewBranching.lean: b37f6b0f99322b5ccda6f646ff4c51e56d2b16ad3b7c01cca29c020e9306545a
- Schur/SkewTableaux.lean: 8be333865524e907fe60dfbff2fb3b58a3cac60986e0f43ec3ae6917fd828a51
- Schur/Tableaux.lean: 11725777aa1405337a0f825ce46b6104a819e592103459590818c312a084cd08
- Examples/TableauBranching.lean: 0c18552e0336083c4bbd58ea3a399e28f3b734ced3c7855836d2d1b09c4b90c0

Base 3781965 plus these four Lean sources; every accepted module was rebuilt and
audited together. KOSTKA is next. The full active goal is not yet complete.
