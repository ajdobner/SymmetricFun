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
