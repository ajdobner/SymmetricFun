# Coefficient functoriality and scalar extension

- Task: BASE; owner: Codex (single worker); status: done.
- Prerequisite API at c62ade0; current base checkpoint e20719b.
- Pin: Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- Scope: `SymmetricFunctions/BaseChange.lean`, integration and handoff.
- Sources: pinned Mathlib polynomial evaluation/map and tensor-product polynomial
  equivalences. No colleague code copied.

## Mathematical contract and proposed interface

For arbitrary commutative semirings R,S and a unital ring homomorphism φ:R→S,
construct `map φ : SymmetricFunction R →+* SymmetricFunction S`, with identity,
composition, scalar and elementary-generator laws. Evaluation is natural under
coefficient maps; use a ring-hom evaluator `eval₂ φ x` when coefficient maps are
not the preselected algebra structure, avoiding hidden scalar-tower assumptions.
For every commutative ring R, construct

```lean
baseChange (R : Type*) [CommRing R] :
  R ⊗[ℤ] SymmetricFunction ℤ ≃ₐ[R] SymmetricFunction R
baseChange_tmul (r : R) (f : SymmetricFunction ℤ) :
  baseChange R (r ⊗ₜ[ℤ] f) = r • map (Int.castRingHom R) f
baseChange_one_tmul_e (n : ℕ) :
  baseChange R (1 ⊗ₜ[ℤ] e (R := ℤ) n) = e (R := R) n
```

The target structure is an R-algebra equivalence, not merely a bijection.
No nontriviality, flatness, characteristic-zero, or torsion-free hypothesis is
allowed. No lambda structure is inferred from this result.

## Statement review before proof search

The implementing worker checked all tensor base rings: integers are the tensor
base, R acts on the left factor, and the output uses its standard R-algebra
structure. The elementary index zero maps to one. Coefficient functoriality
quantifies over arbitrary ring homomorphisms, not just algebra maps. The
coefficient map in the scalar-extension formula is the canonical integer map.
No contract changes are needed.

## Strategy and validation

Use public generator induction to compare ring maps (fix constants explicitly).
Compose polynomial coefficient maps with the presentation equivalences. Compose
`Algebra.TensorProduct.congr` with `MvPolynomial.algebraTensorAlgEquiv ℤ R`
and the inverse presentation for scalar extension. Final elaborated statement review, examples, integration, and axiom audit passed.

## Exported declarations and separate statement review

Exports in `SymmetricFunction`: `ringHom_ext`, `eval₂`, `eval₂_algebraMap`,
`eval₂_e`, `eval₂_e_zero`, `eval₂_e_succ`, `eval₂_eq_eval`, `map`,
`polynomialEquiv_map`, `map_algebraMap`, `map_e`, `map_id`, `map_comp`,
`eval₂_map`, `eval_map`, `comp_eval₂`, `baseChange`, `baseChange_tmul`,
`baseChange_one_tmul_e`, `baseChange_symm_e`, `eval_baseChange_tmul`.

A separate statement-only pass using `#check @...` confirmed that coefficient
maps and evaluation naturality require only commutative semirings, and that
scalar extension has exactly the tensor base ℤ and the A-algebra structure
promised above for every commutative ring A. No nontriviality or flatness
hypotheses occur. All natural elementary indices, including zero, are covered.
No special lambda structure is claimed.

## Supporting API correction and useful failed approach

Basic now supplies `Module R (SymmetricFunction R)` explicitly via
`Algebra.toModule` at priority 1100. At the tensor boundary, the generic integer
module previously won instance search. Although definitionally equal at default
transparency, it did not reconcile with the algebra-derived module through the
type synonym during implicit search: `Semiring (A ⊗[ℤ] SymmetricFunction ℤ)`
failed while the polynomial version succeeded. Priority 1000 still lost to the
generic instance. The explicit instance comes from the existing algebra;
it does not change any operation or the mathematical representation.

## Validation and checked source

- MCP diagnostics: no errors or warnings in BaseChange.
- `lake env lean .scratch/BaseReview.lean`: exit 0; inspected elaborated signatures.
- `python3 scripts/check_project.py`: exit 0; all 8 accepted modules built,
  all 194 declarations passed the transitive axiom audit (only allowed foundations).
  This rebuilt Basic, Grading, Elementary, Foundation examples, BaseChange and root.
- Examples exercise an inverse scalar-extension expression and coefficient mapping
  of `e 0 + e 2 * e 1`, with the public type locally irreducible.
- Root import coverage includes BaseChange; no pin changes or copied colleague code.
- SHA-256 Basic: `7f2599466c19b9ebf4b81ea4a27024155ef4de0864fda8e2fc9e52a7aaacf49e`.
- SHA-256 BaseChange: `58b8dc28330bfbbf70356baa357983a1dcbbc1b771f38fab8016ff012e0d9422`.

All BASE acceptance criteria pass. No remaining BASE obligations. SPEC and
COMPLETE are ready; finite stable realization and later structures remain open.
