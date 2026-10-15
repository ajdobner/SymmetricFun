# Positive power sums and finite compatibility

- Task: NEWTON; owner: Codex (single worker); status: done.
- Prerequisites: COMPLETE d64df18, SPEC 5f7f1c1; base checkpoint e257846.
- Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- Scope: SymmetricFunctions/PowerSum.lean and Finite/Generating.lean, root/docs.
- Sources: Mathlib Symmetric.NewtonIdentities, Sym.equivNatSum, PowerSeries
  coefficient products, and finite subsets. No colleague code copied.

## Mathematical contract and proposed interface

For every CommRing R, define `p : ℕ+ → SymmetricFunction R` by the integral
Newton recurrence
p k = (-1)^(k+1) * k * e k - ∑ (i,j) in antidiagonal k with 0<i<k,
  (-1)^i * e i * p j,
where the filtered antidiagonal ensures 0<j<k. Prove homogeneity of degree k,
specialization to Mathlib psum, and p 2 = e 1 squared minus 2*e 2.
Do not add a stable cardinal-valued p 0.
Also prove rho_N(h n)=Mathlib hsymm (Fin N) R n for every N,n.

## Pre-proof statement review

The power-sum recurrence uses only integral arithmetic, with no division by k.
Its domain is positive indices; all references to recursive p j carry positivity
from the antidiagonal filter. Coefficient rings remain arbitrary, including
nonreduced rings and the zero ring. h 0 specializes to one even for N=0;
positive h and p specialize to zero in the empty alphabet. No completed
symmetric-function type is introduced. Formal univariate generating series,
if used, serve only to prove finite coefficient identities.

## Strategy and preliminary search

Mathlib supplies the exact positive Newton recurrence `psum_eq_mul_esymm_sub_sum`.
It does not yet supply the e/h convolution. Prove that finite complete polynomials
are coefficients of the product of geometric series, using PowerSeries.coeff_prod
and Sym.equivNatSum. Prove the elementary series is the product of (1-X_i*u),
using finite powerset expansion. Their product is one, yielding the finite h
recurrence and the specialization theorem by strong induction. Then construct p
and prove its finite compatibility and homogeneity by the Newton recurrence.
Final elaborated statement review and validation passed; exports follow.

## Exported declarations and separate statement review

`SymmetricFunctions`: `elementarySeries`, `completeSeries`,
`hsymm_eq_sum_finsupp`, `coeff_completeSeries`, `coeff_elementarySeries`,
`completeSeries_mul_elementarySeries`, `esymm_hsymm_convolution`, `hsymm_succ`.

`SymmetricFunction`: `rho_h`, `newtonPairs`, `newtonPairs_spec`, `newtonRight`,
`coe_newtonRight`, `newtonRight_lt`, `p`, `p_rec`, `isHomogeneous_p`, `rho_p`,
`p_one`, `p_two`, `rho_h_empty`, and `rho_p_empty`.

The implementing worker separately reviewed the elaborated declarations with
`#check @...`. The p domain is ℕ+, and newtonRight positivity and strict decrease
are proved from 0<i<k and i+j=k. The coefficient of e k is exactly
(-1)^(k+1) * k. There is no p 0 declaration. rho_h and rho_p quantify over every
alphabet size and retain only CommRing R; both empty-alphabet statements use
positive indices. The finite generating lemmas use Fintype σ and, where required
by Mathlib hsymm, DecidableEq σ. No nontriviality, characteristic-zero or
torsion-free assumption occurs. The h coefficient proof is a finite bijection
between Sym σ n and the exponent antidiagonal; it is not an assumed generating
identity. No mathematical contract changes were required.

## Validation and completion

- Lean MCP final diagnostics: clean for both modules.
- `lake env lean .scratch/NewtonReview.lean`: exit 0; statement-only review.
- `python3 scripts/check_project.py`: exit 0; all 18 accepted modules built cleanly,
  all 439 accepted declarations passed the transitive axiom audit.
- `git diff --check`: passed; both modules in root coverage.
- General low-degree theorem: p 2 = e 1 squared minus 2*e 2. Examples also check
  the rearranged identity and degree two, with the public type locally irreducible.
- SHA-256 PowerSum.lean:
  `863c52ea0cc72b4e4993f2c416d010ed1fb2409f90962ec4359b1f7334667c52`.
- SHA-256 Finite/Generating.lean:
  `35f6b442b11c6d140e1ff7c32e39f1c20ffb874081ce191694928ac63a04c67d`.

All NEWTON acceptance criteria pass. No remaining NEWTON obligations.
HOPF is selected next; LPOLY is independently ready. RELEASE remains open.

Useful elaboration detail: dependent attached sums need an equality of the
attached finset (not only its underlying finset) to simplify small-index cases.
The finite equalities are kernel checked with decide. PNat strong induction has
an internal generated case name in this pin, so use a wildcard case alternative.
