# Finite symmetric polynomial specialization

- Task: SPEC; owner: Codex (single worker); status: done.
- Prerequisite API at c62ade0; base checkpoint 9a38147.
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, unchanged.
- Scope: SymmetricFunctions/Specialization.lean, root and task documentation.
- References: pinned Mathlib Symmetric.Defs and Symmetric.FundamentalTheorem;
  no colleague code copied.

## Mathematical contract and proposed declarations

For every commutative ring R, every N : ℕ, define
`rho R N : SymmetricFunction R →ₐ[R] MvPolynomial.symmetricSubalgebra (Fin N) R`
sending every natural elementary function e k to the k-th finite elementary
polynomial, including k = 0. For k > N it vanishes.

Define `zeroLast R N : MvPolynomial (Fin (N+1)) R →ₐ[R] MvPolynomial (Fin N) R`
by `aeval (Fin.lastCases 0 MvPolynomial.X)`; this sends the last variable to zero
and each castSucc variable to its corresponding variable. Define
`transition R N` on symmetric subalgebras, prove its underlying map is zeroLast,
and prove `transition R N ∘ rho R (N+1) = rho R N` for all functions.
Show the empty-alphabet specialization is the constant polynomial obtained by
evaluating every positive elementary generator at zero.

## Pre-proof statement review

The indices are literal last-variable truncations, not first-variable truncations.
Targets are the symmetric subalgebras, with R-algebra maps. All constants are
fixed, e 0 is one, and N=0 is included. No Nontrivial R hypothesis is permitted.
The finite fundamental theorem is available over arbitrary commutative rings;
using it to show substitution preserves symmetry introduces no field assumptions.
This task makes no injectivity or bounded-degree assertion.

## Strategy and obligations

Reuse multiset elementary polynomials to prove zeroLast sends esymm to esymm.
Use the finite elementary algebra equivalence to restrict the map to symmetric
polynomials. Verify the actual substitution formula, then use public generator
extensionality for compatibility. Final statement review and validation passed.

## Exported interface and final statement review

Exports in `SymmetricFunction`: `rho`, `rho_e`, `rho_e_eq_zero`, `zeroLast`,
`zeroLast_X_last`, `zeroLast_X_castSucc`, `zeroLast_esymm`, `rho_zero`,
`transition`, `coe_transition`, `transition_esymm`, `transition_comp_rho`,
`transition_rho`, and `zeroLast_rho`.

A separate statement-only pass using `#check @...` confirmed that rho and raw
substitution require only CommSemiring R; transitions on the symmetric
subalgebras use CommRing R, as promised. The transition formula identifies its
underlying map for every symmetric polynomial, not only generators.
Compatibility is an equality of algebra homomorphisms and a pointwise theorem.
The empty-alphabet formula uses evaluation at zero on all positive generators.
No Nontrivial instance, field hypothesis, or injectivity assertion was introduced.

## Validation and completion

- Lean MCP declaration search and final diagnostics: no errors or warnings.
- `lake env lean .scratch/SpecReview.lean`: exit 0; elaborated types reviewed.
- `python3 scripts/check_project.py`: exit 0; all 9 accepted modules built cleanly,
  all 213 declarations passed the transitive axiom audit.
- Examples: empty alphabet for arbitrary functions and e 2 + e 0 in one variable;
  the public type is locally irreducible.
- `git diff --check`: passed; root import covers Specialization.
- Source SHA-256: `2ebe23529e195ac8a3b579d47567554155f45a179a9bdc41c5d28dfbcffa25b4`.
- All SPEC acceptance criteria passed. No remaining SPEC obligations.

Proof detail: unrestricted simp expands Fin.univ into a list before the multiset
zero-cons lemma can match. Use simp only with Fin.univ_castSuccEmb and the
lastCases equations. Cancel esymmAlgEquiv.symm before unfolding its forward map.

FINITE and COMPLETE are ready. COMPLETE is selected next for the integral
recurrence and subsequent omega API; the stable realization remains open.
