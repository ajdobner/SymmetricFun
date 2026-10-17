# Existing symmetric function work

Audit date: 2026-10-14. Source: `/home/ghseeli/SymmetricFun`, commit `98938de95a12b3ed363653cb980588e2a9188cb8`. Its manifest pins Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` and Lean `v4.30.0`.

This is a source audit, not a successful build report. The checkout has no `.lake` directory. There are 11 non-root Lean files, totaling 1,378 lines. A textual scan found 18 occurrences of `sorry` in eight files. A declaration without a local hole may still depend on one elsewhere.

The most directly useful file is `SymmetricPoly/SymmFunc/Basic.lean`. Despite the README emphasizing power series, this file already takes the polynomial approach accepted for the new project.

| Source file under SymmetricPoly | Useful material | Integration decision |
| --- | --- | --- |
| `SymmFunc/Basic.lean` | `SymmFunc R := MvPolynomial ℕ+ R`, weighted homogeneous pieces, graded algebra, `e`, `ePart`, general weighted monomial basis | First port candidate. Finish partition multiplicities and the elementary basis. Replace the public abbreviation with the dedicated type and controlled equivalence chosen in API. |
| `Finsupp/SymmetricAction.lean` | Permutation action; classification of finite exponent vectors by the multiset of nonzero exponents | Adapt orbit lemmas when building the monomial basis or series realization. Avoid importing its custom partition dependency wholesale. |
| `MvPowerSeries/Homogeneous.lean` | Homogeneous submodules, graded multiplication, bounded-degree subalgebra | Optional series bridge. The equivalence with coefficientwise bounded degree and the finite polynomial range theorem have holes. |
| `MvPowerSeries/Symmetric.lean` | Permutation action, coefficient transport, fixed-point subalgebra | Useful later, after reconciling with the chosen Mathlib version. `isSymmetric_C` is unfinished. |
| `MvPowerSeries/HomogeneousSymmetric.lean` | Intersection defining bounded symmetric series | A good semantic target for a later equivalence; depends on unfinished earlier lemmas. |
| `MvPowerSeries/Bases.lean` | Monomial series defined by exponent shape, coefficient extraction, proposed monomial basis, formulas for elementary and complete series | Reuse proof ideas. Three holes remain; the basis is not certified. |
| `Combinatorics/Enumerative/Partition/Basic.lean` | Unsized `Nat.GenericPartition` and size-indexed partitions | Do not import as a replacement for Mathlib. It redeclares `Nat.Partition` and other existing names. Extract useful adapter lemmas into fresh namespaces. |
| `Partition.lean` | Separate sorted-list partitions, interlacing, fusion-specific bounds | Defer. Establish explicit equivalences before any eventual use. Two finiteness instances are unfinished. |
| `DecomposableAddMonoid.lean`, `TotalMonoidAlgebra.lean` | Finite decomposition sums and convolution algebra | Outside the initial critical path. No textual holes found, but not compiled or dependency-audited. Do not undertake a general power-series refactor for the initial milestones. |
| `FusionRing.lean` | A separate downstream research direction | Defer. Contains five holes and depends on additional partition/Schur infrastructure. |

The polynomial prototype's comment says to seal the definition with a structure, but its actual declaration is an `abbrev`. Treat that comment as a design intention, not an implemented abstraction boundary.

The root `SymmetricPoly.lean` is empty. Existing CI invokes Lean tooling, but the source audit does not establish which files its build covers. Our new CI must enumerate accepted modules or verify an exhaustive root import and build it.

The manifest's top-level project name is `LeanFusion`, while the Lake package is `SymmetricPoly`. Regenerate the manifest in a fresh port workspace rather than copying this metadata blindly.

Some source has Mathlib Apache headers, but no repository-wide license file was found. Preserve existing headers and commit provenance. Establish the license for colleague-authored material before redistribution; this does not prevent inspecting ideas or planning the port.

Port order:

1. Isolate the weighted monomial basis lemma and partition multiplicity equivalence.
2. Adapt the polynomial representation, grading, and elementary API.
3. Add finite specialization using Mathlib's fundamental theorem, rather than proving polynomial freeness via Gale–Ryser.
4. Reuse exponent-orbit arguments for the monomial basis if they shorten the finite-variable proof.
5. Add the power-series realization after the core ring, Hopf, and lambda targets. Keep it equivalent to the accepted public type.

## MONOMIAL implementation reuse

The pinned Mathlib already defines `MvPolynomial.msymm` from `Nat.Partition`
and proves its permutation invariance. MONOMIAL directly reuses that sum,
`Sym.equivNatSum`/multiset multiplicities, `killCompl`, and the multiset
occurrence type. New local proofs establish its exact coefficients, stability,
and basis. The colleague's support-fiber matching idea in
`SymmetricPoly/Finsupp/SymmetricAction.lean` (98938de95a12b3ed363653cb980588e2a9188cb8)
is credited in `Partition/Orbits.lean`; proofs were reconstructed with Mathlib
APIs, without copying colleague source or importing its replacement partitions.
The unresolved redistribution-license caution for colleague source is unchanged.

## RATIONAL implementation reuse

The rational power-sum presentation reuses the local integral Newton recurrence,
Mathlib algebra equivalences/evaluation, and the proved elementary partition
bases. Tensor and mixed presentations reuse `MvPolynomial.tensorEquivSum` and
`Algebra.TensorProduct.congr`; parameter Adams uses `MvPolynomial.expand`.
The geometric example uses the pinned rational-function polynomial embedding.
The paper's coefficient and plethystic conventions were consulted read-only.
No colleague proof text, replacement partition definition, external proof, or
new dependency was imported. See `handoffs/RATIONAL.md` for statement review
and full validation.

## SERIES implementation reuse

Consulted the colleague's Homogeneous, Symmetric, HomogeneousSymmetric and Bases
modules read-only. Their invariant-series and proof-irrelevant bound design and
coefficient-shape approach are credited in Realization/SeriesBasic.lean. No proof
text or replacement partition was copied. The new equivalence uses the proved
local monomial basis and orbit classification, pinned MvPowerSeries.rename,
killCompl, polynomial inclusion and homogeneousComponent. All referenced
proofs are in the accepted dependency graph and pass the axiom audit.

## COMPLETION implementation reuse

Completion uses the pinned Mathlib PowerSeries algebra to establish finite
antidiagonal convolution on the product of the existing weighted homogeneous
pieces. Equiv transport transfers proved algebra laws; no new algebra axiom is
postulated. The symmetric-series equivalence reuses this project's monomial-basis
SERIES realization. Completed coproduct reuses the proved total tensorDegree and
comultiplication homogeneity. The e/h inverse identities reuse COMPLETE's finite
convolutions. Certified evaluations use Mathlib HasSubst, substAlgHom,
coeff_subst_finite and truncTotal_subst_eq_truncTotal_subst_sum, discharging all
actual hypotheses, including coefficientwise finiteness for infinite alphabets.
No new colleague implementation text was copied, no reference checkout was
modified, and the pinned dependencies are unchanged.

## SCHUR checkpoints: partition and determinant foundations

Reuse pinned Mathlib `YoungDiagram.ofPartition`, `Nat.Partition.conjugate`,
`SemistandardYoungTableau`, finite determinant expansion and adjugates. New proofs
use these public APIs and the project's existing h/e convolution; no colleague
source was copied and both reference checkouts remain unchanged. The new finite
upper Toeplitz ring map proves its multiplication by an explicit interval-to-
antidiagonal bijection. A search of the pin found no Jacobi–Trudi implementation.

## SCHUR completed algebraic theory

The integral basis uses pinned Mathlib rearrangement, determinant, basis, and
direct-sum APIs. Complementary minors use block determinants and the actual
h/e Toeplitz inverse, with explicit Mathlib YoungDiagram boundary and permutation
sign proofs. Hall theory uses the established actual monomial basis, finite
coefficient orbits, finite margin matrices and their transposes; Schur
orthogonality uses an integral bialternant multiplication identity, with no
alternant division. Skewing contracts the proved finite Hopf coproduct; its
skew determinant follows from mixed-alphabet coefficients and finite column
separation. The Cauchy product uses pinned MvPowerSeries.invOfUnit and certified
PowerSeries.substAlgHom, and Finsupp.image_sumElim_product_antidiagonal proves
the joint/iterated series algebra equivalence. All infinite-looking expressions
are handled coefficientwise by finite antidiagonals or actual HasSubst proofs.
No colleague proof text, replacement shape definitions, dependency changes,
external proving services, or reference-checkout edits were introduced.

## Tableau foundations

The pin contains Jake Levinson's `SemistandardYoungTableau`, its row/column and
outside-zero API and `highestWeight`, but no straight/skew Schur weight formula,
Kostka API or skew-tableau adapter was found. Reuse is by import. The new finite
alphabet instance is proved by injection into functions from the existing finite
cell set to Fin N. Content and weights are reconstructed with finite sums and
Mathlib monomials; no colleague proof text is copied. The paper's diagrams and
tableaux section was read for zero-based/French convention documentation only.
Both reference checkouts and the dependency pins remain unchanged.

## Kostka continuation

The pinned partition/YoungDiagram and tableau APIs were searched for dominance
and Kostka declarations; no existing API was found. New `rowContent` is an
adapter for Mathlib's decreasing partition rows, not a replacement partition.
The diagonal and prefix inequalities use actual finite cell fillings, Mathlib
finite-sum order lemmas, and the existing highest-weight tableau. Alphabet and
orbit independence reuse the project's proved monomial basis coefficient API.
All code here is newly written; no colleague source was copied, no reference
checkout was modified, and the dependency pins remain unchanged.
