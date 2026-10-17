# Dual Jacobi–Trudi and conjugation

Task SCHUR-DUAL, owner Codex (single worker), status done. Dependencies
SCHUR-JT and OMEGA complete; integral Schur bases now complete at 4ba39c0.
Pins unchanged. Ownership Schur/Dual.lean and helper
Schur/ComplementaryMinors.lean; additional shape-boundary helpers will be recorded
before implementation if needed.

## Proposed contracts and review before proof search

`elementaryInt (k : ℤ)` is zero for k<0 and e_(k.toNat) otherwise. The dual
Jacobi–Trudi formula is
`schur ξ = det (fun i j : Fin L => elementaryInt
 ((rowLength ξ.conjugate i : ℤ) - (i : ℤ) + (j : ℤ)))`
for every L≥length ξ.conjugate. The resulting theorem
`omega_schur ξ : omega (schur ξ) = schur ξ.conjugate` uses Mathlib conjugation.
These are arbitrary-CommRing identities, including the empty shape. A determinant
of elementary functions indexed by ξ itself is omega(schur ξ); it must not be
mistaken for the dual formula indexed by ξ.conjugate before proving the bridge.

Generic helper: for finite types I,J and matrices A,B indexed by I⊕J over a
CommRing, if A*B=1 then det(A.toBlocks₁₁)=det(A)*det(B.toBlocks₂₂).
This follows from A*[1 B₁₂;0 B₂₂]=[A₁₁ 0;A₂₁ 1]. No fraction field, scalar
cancellation, or invertible proper subblock is required. This will be applied to
the h/e Toeplitz inverse matrices after explicitly verified shape reindexing.
The reindexing complements and signs are substantive remaining proof obligations,
not implicit in the generic block lemma.

## Pinned reuse search

Matrix.fromBlocks_multiply, det_fromBlocks_zero₁₂/₂₁, det_mul, and determinant
reindexing/sign APIs. The pin has adjugate one-row/column minor formulas but no
searched general complementary-minor formula. Use the already proved finite
upperToeplitzHom and h/e generating inverse; no analytic or infinite substitution
is involved. Do not mark this task complete at the elementary-matrix bridge.

### Reviewed shape-boundary adapter

Use existing YoungDiagram columns for the complement. Put l=length ξ,
w=rowLength ξ 0. The selected row addresses are
A_i=w-rowLength ξ i+i for i<l; complement addresses are
C_j=j+(YoungDiagram.ofPartition ξ).colLen(w-1-j) for j<w.
Both lists are strictly increasing and contained in [0,l+w). Their disjointness
is exactly the equivalence between row and column membership of the cell
(i,w-1-j). Therefore their concatenation is a bijection to Fin(l+w). This is an
address adapter, not a partition or conjugation definition. Natural subtraction
here is justified by rowLength ξ i≤w and j<w; determinant indices remain integers.
Ownership extends to Partition/Boundary.lean. The permutation sign and final
complement identification remain separate obligations after this bijection.

### Ordered shuffle sign helper

For `e : Fin l ⊕ Fin w ≃ Fin(l+w)` increasing separately on each summand, prove
`sign (finSumFinEquiv.symm.trans e) = ∏i ∏j (if e(inl i)<e(inr j) then 1 else -1)`
in the integer units. Pinned `Equiv.Perm.sign_eq_prod_prod_Ioi` (Perm/Fin) reduces
this to the four pairs of summands. The two internal blocks have no inversions.
For boundaryEquiv the cross condition is exactly cell membership proved above;
for the tail-first column ordering it is always false. This will account for
all signs explicitly. Scope additionally Schur/ShuffleSign.lean.

## Accepted implementation and separate statement review

`dual_jacobiTrudi` proves the actual elementary determinant on ξ.conjugate for
all sufficient padding; `omega_schur` proves omega(schur ξ)=schur ξ.conjugate.
`elementaryInt` is zero at negative indices and one at zero. Both formulas
retain only CommRing assumptions. The empty shape is included.

The generic complementary-minor proof uses A*B=1 and block multiplication.
The YoungDiagram boundary lists are proved complementary and strictly increasing.
`sign_orderedShuffle` reuses the pinned inversion-product formula, and
`sign_boundary_relative_tail` counts the exact partition-size sign. The signed
E minor contributes the same sign; their product is one in every ring. No
proper-minor cancellation, domain, field, rationality, or Nontrivial assumption
is hidden. The finite inverse comes from the existing proved generating identity.

ReviewSchur printed the definitions, complement hypothesis, row/column address
bijection, sign, padding hypothesis, and final conjugation type. These were
reviewed separately from the proof scripts and match the intended mathematics.
The tableau bridge and all positivity claims remain separately unproved.

## Validation and exact source state

Base 4ba39c0 plus this checkpoint. SHA256:
- Schur/Dual.lean: e2540b23ab5c1c42945ec6c3298a86ae88043f220985fa36a3b78b120f54b45b
- Schur/BoundarySign.lean: 4da1b57b9ebdf3a0be1d2c71673b58f91401bf0e08a941f20b6cb41bb89303ea
- Schur/ComplementaryMinors.lean: 831a67085bdd0ff3f7380485cb6318652f0e86e1fe76dce03d0c99d993bf0c2d
- Schur/ShuffleSign.lean: 11fe20cd81089b817a1d78b0ace876fa10989171e57571ce8daed7426bc8e4e8
- Partition/Boundary.lean: e785188603e79a068e5e865c96d6e37af2bd39dc86548a28e92a6b4a2dcad10d
- Examples/SchurDual.lean: 7273af3910218f9429f6be089c728c0565f0a201a52e3f583788d612f5851efa

`python3 scripts/check_project.py`: exit 0, 104 accepted modules, 1,893 transitive
axiom checks; notation and lambda regressions pass.
`python3 scripts/test_check_project.py`: exit 0, five tests.
`lake env lean scripts/ReviewSchur.lean`: exit 0, only approved standard axioms.
Lean MCP examples diagnostics: success with no errors or warnings. Examples
check negative indices, empty padding, rows/columns, and the proved self-conjugacy
of (2,1), including omega invariance over ZMod 6.

Useful Lean detail: normalize `Matrix.of_apply` in the row-scaling determinant
lemma before rewriting nested Matrix.of expressions. Passing the inner matrix
as a raw lambda can produce transparency mismatches. No option change is needed.

No SCHUR-DUAL obligations remain. Next HALL-CORE; classical Hall normalization,
symmetry, degreewise perfectness and Hopf adjunction still need implementation.
