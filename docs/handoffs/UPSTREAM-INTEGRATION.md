# Upstream integration

- Owner: Codex (single worker); task UPSTREAM-INTEGRATION; status review (proofs accepted; publication pending).
- Sources: local 0bd3a94 and upstream 5b32dda72cfc38e21c32df14ac2b25cb8b4910ba.
- User requested merging Alex’s changes and a PR back to his repository, preferring his intentional design choices.

## Contract and design review

Keep Alex’s `SymmetricFun` package, primary bounded-power-series subalgebra, internal grading, arbitrary variable types, existing partitions, and local permutation actions. His proved `MvPowerSeries.esymmAlgEquiv` supplies a polynomial presentation for every infinite alphabet and commutative coefficient ring. Connect the existing polynomial-backed development by composing this equivalence with its public `polynomialEquiv`; prove generator, grading, and natural-alphabet series compatibility. Neither implementation is silently redefined. The existing polynomial-backed type remains a compatibility surface for proved downstream results; the upstream power-series definition remains the native foundation.

Adopt Lean v4.35.0 and the exact upstream manifest. Validate all sources against this recorded environment change. Preserve upstream source and attribution; no new license is asserted. The former SymmetricPoly drafts were deliberately removed upstream and remain removed. Both accepted library trees must be built and audited, including declarations not used by the bridge.

## Accepted formal interface

For `CommRing R` and `Infinite σ`, provide `SymmetricFunction.upstreamEquiv σ R : SymmetricFunction R ≃ₐ[R] MvPowerSeries.symmetricFunctionSubalgebra σ R`, with elementary-generator and weighted-homogeneity formulas. For σ = ℕ, its underlying series must equal `SymmetricFunction.toSeries R`. Read both definitions independently before accepting these correspondences.

## Statement review and exported declarations

Single-worker review used `scripts/ReviewUpstreamIntegration.lean` to inspect the actual carriers, boundedness predicate, equivalence definition, theorem types, and transitive axioms. The arbitrary-alphabet bridge requires `Infinite σ` and `CommRing R`; it neither claims the fundamental theorem for finite alphabets nor restricts coefficients to characteristic zero. The coefficientwise comparison uses σ = ℕ. The upstream CommSemiring foundation is unchanged. Homogeneity means weighted degree, not ordinary polynomial degree.

Exported from `SymmetricFunctions.Compatibility.Upstream`:

- `SymmetricFunction.upstreamEquiv`, `upstreamEquiv_e`, `coe_upstreamEquiv_e`.
- `upstreamEquiv_mem_grading_iff`, `upstreamEquiv_homogeneousComponent`.
- `MvPowerSeries.coe_polynomial_esymm`.
- `SymmetricFunction.toSeries_e_eq_upstream`, `coe_upstreamEquiv`.
- `coe_upstreamEquiv_h`, `upstreamEquiv_h`, `coe_upstreamEquiv_mPart`.
- `boundedSymmetricSubalgebra_eq_upstream`.

`Partition.Dominates` now abbreviates upstream `Nat.Partition.Dominates`. The proved `dominates_iff_prefix_rows` retains the previous explicit row-prefix inequalities; the Kostka vanishing statement keeps its direction and hypotheses.

## Proof strategy and useful failed approaches

Compose the existing polynomial equivalence with upstream's fundamental theorem. Transfer grading using its exact weighted-homogeneity theorem. Prove elementary series agreement coefficientwise, then use algebra-hom extensionality on elementary generators for the whole natural-alphabet map. Compare complete functions through finite truncations and monomials through their coefficient formulas.

A finite-complete coefficient rewrite initially passed a direct `lake env lean` check but failed the package build because the theorem and target used different `DecidableEq (Fin N)` instances. The final proof explicitly identifies these subsingleton instances before rewriting. Use `lake build` with the package options as the authoritative module check.

## Validation and integration

All commands below completed with exit 0 on Lean v4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679:

- `lake build SymmetricFunctions.Compatibility.Upstream SymmetricFunctions.Examples.Upstream`: bridge and native-operation examples compile.
- `python3 scripts/check_project.py`: 50 tasks, 165 accepted modules; every module explicitly built, full build completed (2835 jobs); all 2872 accepted declarations transitively audited. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. Notation and lambda-simplification checks also passed.
- `python3 scripts/test_check_project.py`: all 8 regression tests pass, including native-module omissions, upstream proof holes, and transitive facade coverage.
- `lake env lean scripts/ReviewUpstreamIntegration.lean`: actual contracts and selected axiom dependencies checked.
- `lake env lean scripts/DeclarationIndex.lean`: 2044 noninternal declarations indexed in `docs/declarations.tsv`.
- `git diff --check`: passed. The native `SymmetricFun/` tree, `SymmetricFun.lean`, toolchain and manifest have no differences from upstream 5b32dda.

Examples exercise native elementary-to-complete involution, integral exterior powers including index zero, complete functions over ZMod 6, grading over the zero ring ZMod 1, and arbitrary infinite alphabets.

The build emits nonblocking header and legacy-module import style warnings. No proof placeholders or unapproved axioms were accepted. Existing historical handoffs retain their earlier pins; this combined check validates the merged source against the new pins.

## Remaining boundary and publication

The extension theorems still use their existing polynomial-backed type; the proved equivalence exposes them to native clients. This integration does not yet restate every theorem for arbitrary native alphabets or install global native Hopf/lambda instances. See `docs/INTEGRATION.md` for the design decisions and review entry points. No reference checkout was changed and no license was invented.

The exact accepted Lean source state is recorded below. Publication to the fork and the PR against Alex's main remain pending; the task will be marked done once those succeed.

```text
8b669d64bb77b5ba03117d64ae73651357561cfbb28fbc86c1eba22e3be4b593  SymmetricFunctions/Compatibility/Upstream.lean
b9d4d59d0701c255f03bacd0fad30d3c87bbc3b28f5d4f24c90a40a275156a4a  SymmetricFunctions/Examples/Upstream.lean
283f322633d19266ff2b9ffa191ee8f3d48946b6bd0eeb9b934b855a57adfe43  SymmetricFunctions/Tableaux/Kostka.lean
da2b103eab8a7d9e9719c9f548bf355b8a8c0a180bd950c415871400a0dac05d  SymmetricFunctions/Examples/Kostka.lean
```
