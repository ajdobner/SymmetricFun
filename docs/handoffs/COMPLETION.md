# Degree completion, Omega, and valid evaluation

- Parent task COMPLETION; owner Codex (single worker); status in_progress.
- SERIES complete at 2fa2390; COMP-ALG complete in the following checkpoint. Pins unchanged.
- Subtasks COMP-ALG, COMP-SERIES, COMP-OMEGA, COMP-HOPF, COMP-SUBST preserve
  every original parent acceptance criterion; see docs/tasks.json.

## Reviewed mathematical contract before implementation

The completed type is the product `∀ n : ℕ, homogeneousSubmodule R n` over
arbitrary CommRing R. Its multiplication has degree-n component
`∑ (i,j) in antidiagonal n, F_i * G_j`, with membership proved by weighted
homogeneity. Zero-degree scalars provide the R-algebra structure. Bounded
functions embed by their homogeneous components, injectively. Truncation is
the finite sum of components through a specified degree, and multiplication
agrees below that degree. The completion is algebra-equivalent to permutation-
invariant MvPowerSeries ℕ R, with no uniform bound imposed.

`completeSeries` has component h_n. Scoped Ω denotes this completed element;
ω continues to denote the bounded elementary-complete involution. The signed
series with component (-1)^n e_n is a two-sided inverse, by the existing finite
convolution identities. The completed tensor target must count both factor
degrees, allow infinite total-degree support, and use finite antidiagonal
convolution. Extend the actual Hopf coproduct and prove Ω group-like there;
no ordinary algebraic tensor-product codomain assertion is allowed.

Completed evaluation requires a proved coefficient-finiteness or filtration
hypothesis. Mathlib HasSubst includes both constant-term and family-finiteness
conditions, and its underlying dummy function outside these conditions must
never be exposed as a valid evaluation. Bounded agreement and useful Ω examples
are required. Merely inverting every 1-t^k does not establish convergence of Ω.
No unrestricted infinite plethysm is part of this contract. No rationality is
needed for the general completion or Hopf results.

Detailed interfaces, statement reviews and validation will be recorded in each
subtask handoff before long proof searches. The parent remains unfinished until
all subtask criteria and integrated examples pass. SCHUR remains outside this run.
