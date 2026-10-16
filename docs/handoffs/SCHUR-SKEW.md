# Bounded adjoint skewing and actual skew Jacobi–Trudi determinants

- Owner Codex (single worker); status in_progress; base e1d92b4.
- Prerequisites HALL-SCHUR, SCHUR-DUAL, SCHUR-PART complete.
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 pinned.
- Assigned Hall/Skewing.lean, Schur/Skew.lean, Hopf/MixedSpecialization.lean,
  Schur/SkewDeterminant.lean, Examples/SkewSchur.lean.

## Precise proposed interfaces and pre-proof review

All coefficient assumptions are CommRing R, including torsion and zero rings.
`hallContraction f : SF R ⊗[R] SF R →ₗ[R] SF R` maps x⊗y to hall(f,y) • x.
`skewing f : SF R →ₗ[R] SF R` is hallContraction f after the existing coproduct.
Its defining theorem is `hall (skewing f g) h = hall g (f*h)` for all bounded
f,g,h. The finite algebraic coproduct makes the output bounded; no identification
with the full algebraic dual or infinite summation is involved. Prove uniqueness,
linearity in the skewing argument, skewing_one, composition, and degree behavior:
homogeneous degrees a,b yield degree b-a, and zero if b<a.

`skewSchur ξ μ := skewing (schur μ) (schur ξ)` allows different shape sizes.
`skewJacobiTrudiMatrix ξ μ L` has entry
`completeInt ((rowLength ξ i : ℤ) - (rowLength μ j : ℤ) - (i : ℤ) + (j : ℤ))`.
The actual determinant equals skewSchur at every L at least both lengths,
including noncontained shapes. Prove skewSchur_empty, skewSchur_self=1,
skewSchur_eq_zero_of_not_contained using the existing YoungDiagram containment,
and the coproduct formula with partitions μ of sizes ≤size(ξ):
Δ(s_ξ)=Σμ skewSchur ξ μ ⊗ s_μ. The finite index set is explicitly
(range(size ξ+1)).sigma (fun _ => univ); it is not an undefined infinite sum.

Statement review: all determinant casts precede subtraction. The skew shape is
an adjoint applied to the already proved actual Schur function. Any determinant
formula must be a theorem, not a redefinition. Degree b-a alone does not assert
vanishing when b<a; that vanishing is a separate obligation. Containment refers
to YoungDiagram. Empty/equal conventions include size zero. No LR positivity
or tableau formula is asserted.

## Planned proof route / reuse search

Mathlib supplies TensorProduct.lift and LinearMap.lsmul; HALL-CORE supplies the
explicit tensor pairing and both adjunction orientations. Use contraction and
Hall nondegeneracy. Degree behavior can use the proved total tensorDegree span
and comultiplication_mem_tensorDegree, or Schur coordinate orthogonality.

For the skew determinant, specialize only the right tensor alphabet into
MvPolynomial (Fin L) (SF R), leaving the left factor as coefficients. Prove
this actual algebra map and its tensor formula. Alternating coefficient
extraction in the right alphabet realizes contraction by schur μ. The complete
series of the sum alphabet is H_left * H_right. Multiplication by the existing
omitted-variable coefficient matrix cancels H_right's other factors, leaving
H_left times the geometric series in a single right variable. Determinant
coefficients then separate by columns, giving h_(ξ_i-μ_j-i+j) exactly. This
avoids assuming an absent rectangular Cauchy–Binet or a tableau formula.

Remaining obligations: entire task in progress. No claims of completion until
exact declarations, independent statement review, all accepted module/axiom
checks, checker tests, examples, guides and checkpoint are recorded below.

## First coherent checkpoint: bounded adjoints and finite coproduct expansion

Accepted modules Hall/Skewing.lean, Schur/Skew.lean and Examples/SkewSchur.lean
now prove hall_skewing, skewing_unique, skewing_one/zero/add/smul/mul,
isHomogeneous_skewing, skewing_eq_zero_of_degree_lt, skewSchur_empty/self,
isHomogeneous_skewSchur, skewSchur_eq_zero_of_size_lt, and comultiplication_schur.
The last theorem uses a genuinely finite sum over n∈range(d+1) and Partition n.
The skew matrix is defined with the exact proposed integer indices; there is
not yet a theorem identifying its general determinant with skewSchur.

Separate statement review (Codex): contraction keeps the first factor and pairs
the second with f. Tensor Hall symmetry and the existing adjunction give exactly
hall(f-perp g,h)=hall(g,fh). Arbitrary rings and boundedness are retained. Both
degree b-a and vanishing below a are proved, without a natural-subtraction gap.
Equal/empty shape results refer to the adjoint definition, and the coproduct
sum has an explicit upper degree bound. No determinant or noncontainment theorem
is claimed prematurely. `skewing_apply` remains a non-simp implementation bridge
so the public identity/zero normal forms work without unfolding contraction.

Validation (all exit 0): python3 scripts/check_project.py (117 accepted modules,
2,057 transitive axiom audits; only propext/Classical.choice/Quot.sound; notation
and lambda regressions pass); python3 scripts/test_check_project.py (five guards);
lake env lean scripts/ReviewSchur.lean (printed definitions/types independently
reviewed); lake env lean scripts/DeclarationIndex.lean (1,479 noninternal entries).
MCP Hall/Skewing and Examples/SkewSchur diagnostics clean. git diff --check clean.
Logs: /tmp/skew-adjoint-{check,review}.log. Pins/reference checkouts unchanged.

Exact checked Lean source SHA-256:
- `Hall/Skewing.lean`: `c9dbaa0d05bfc945dbbff7c0504477edc9ece10efdf29ba46971d4f7971e33f4`
- `Schur/Skew.lean`: `b05687ab1b94e620e36ba38daba1a4ed45ac1eb8a59fdd324fd6dc3ce824b2db`
- `Examples/SkewSchur.lean`: `0feebb349f9cde3a6b4018c1fa1f3f2d6e957de222b72bda20f941884ec382cf`

SCHUR-SKEW remains in_progress. Next action: implement the actual right-alphabet
specialization into MvPolynomial (Fin L) (SF R), prove its complete-series
identity and alternating coefficient contraction. Then the column-separated
matrix coefficient calculation gives the general skew determinant, followed
by YoungDiagram noncontainment vanishing and full validation.
