# Degree-completion algebra and truncation

- Task COMP-ALG; owner Codex (single worker); status done.
- Prerequisites SERIES 2fa2390 and GRADE complete; pinned environment unchanged.
- Scope Completion/Graded and Completion/Basic.

## Proposed precise interfaces and statement review

For a commutative R-algebra A and submodules G : Nat -> Submodule R A with
SetLike.GradedMonoid G, define `GradedCompletion G := ∀ n, G n` as a separate
type synonym, not the pointwise-product ring. Build the algebra through its
bijection with the subalgebra `{F : PowerSeries A | ∀n, coeff n F ∈ G n}`.
The latter is closed under Cauchy multiplication by graded multiplication and
the finite antidiagonal. This establishes all algebra laws without positing them.
Expose component equality, component addition/scalar rules, and
`component (F*H) n = ∑ij in antidiagonal n, component F ij.1 * component H ij.2`.
This infrastructure also applies to the already proved total tensorDegree.

For G = SymmetricFunction.homogeneousSubmodule R define `DegreeCompletion R`.
`completionEmbedding R : SF R ->ₐ[R] DegreeCompletion R` sends f to its genuine
homogeneous projections. Prove multiplicativity via the existing direct-sum
grading, injectivity by finite reconstruction. Truncate through D by summing
components at indices ≤D into SF R. Prove its components are the original ones
below the cutoff and zero above; truncation of products agrees after truncating
both factors and truncating the result. No polynomial-generator ordinary degree
or uniform bound on the completed carrier is used.

The implementing worker reviewed the product carrier, the role of the auxiliary
series variable (only to prove convolution laws), scalar placement in degree
zero, the inclusive cutoff convention, and arbitrary CommRing R including zero.
A generic degree-preserving algebra map should act componentwise and preserve
convolution; this will support completed coproduct without assuming an ordinary
tensor product of completions suffices. No completion theorem is assumed.

## Search and validation plan

Pinned Mathlib PowerSeries coefficient multiplication, subalgebras and
Equiv.algebra/commRing provide the algebra proof. DirectSum.decompose_mul and
its finite coefficient formula supply bounded embedding multiplication. Use
public component lemmas afterward. Validate and review all exported contracts,
run project checker and guard tests, update index/docs and commit when complete.

## Exported declarations and independent statement review

`GradedCompletion.seriesAlgEquiv`, `toPowerSeries`, `component_mul`, `map`
prove the auxiliary algebra and degree-preserving functoriality. The public
specialization exports `DegreeCompletion`, `completionEmbedding`, its
injectivity, `homogeneousComponent_mul`, `DegreeCompletion.component_homogeneous`,
`truncate`, `homogeneousComponent_truncate`, `truncate_mem_degreeLE`,
`truncate_eq_iff`, `truncate_mul`, `truncate_truncate`, and
`truncate_completionEmbedding_of_degreeLE`.

A separate pass with scripts/ReviewCompletionAlgebra.lean inspected elaborated
statements and the carrier definitions. Every general result uses CommRing R,
with no nontriviality or rationality assumption. Component membership refers to
the original weighted homogeneousSubmodule. Multiplication adds both component
degrees; it is not inherited pointwise multiplication of a Pi type. The scalar
map has support at degree zero. Truncation is inclusive and becomes multiplicative
only after truncating the product again; no false algebra-hom claim is made.
The bounded embedding uses the proved direct-sum projections and is injective.

## Validation

- `python3 scripts/check_project.py`: exit 0; 80 accepted modules built and
  transitive axioms of 1,525 declarations audited, only ordinary Lean foundations.
- `python3 scripts/test_check_project.py`: exit 0; all five tests passed.
- `lake env lean scripts/ReviewCompletionAlgebra.lean`: exit 0.
- Lean MCP diagnostics for Completion/Basic: clean.
- Examples cover degree-three elementary functions, degree-zero convolution,
  inclusive truncation, torsion coefficients and the zero ring. A formatting-only
  long-line fix was followed by rebuilding the examples and root.
- `lake env lean scripts/DeclarationIndex.lean`: refreshed accepted index.

No remaining COMP-ALG obligations. COMP-SERIES is next; the completion's symmetric
series identification, Omega, completed coproduct and evaluation remain open.

Checked source hashes (SHA-256):
- `SymmetricFunctions/Completion/Graded.lean`: `ee228c2a27f2e62e77e51155f2820178cabb034d949147c91e495f053fe8aa97`
- `SymmetricFunctions/Completion/Basic.lean`: `c3442e96c0f23def1c15455b0729a9f6319f0a972f089d7cdbfb78df4e954c78`
- `SymmetricFunctions/Examples/Completion.lean`: `04c6ab0ff35b2602e6823cf82033972713796c012ce95ebb925e979ff691f105`
