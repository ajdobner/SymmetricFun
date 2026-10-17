# Agent instructions

Read `docs/ROADMAP.md`, the selected entry in `docs/tasks.json`, and any relevant handoff before editing Lean code. Consult `docs/REUSE_AUDIT.md` before porting colleague code. This repository is a fork of ajdobner/SymmetricFun. The accepted libraries are SymmetricFun (the native power-series foundation), SymmetricFunctions (the connected extension API), and LambdaRing. The obsolete SymmetricPoly drafts were removed upstream.

## Mathematical contracts

- Defer to the upstream bounded-power-series foundation, internal grading, package layout, and local permutation actions. Preserve the polynomial-backed extension API and its proved equivalence as a compatibility surface; do not silently redefine either carrier or migrate existing contracts. See docs/INTEGRATION.md.
- The proposed internal generator index is `ℕ+`, matching the colleague's prototype. Public elementary and complete functions have natural-number indices with `e 0 = h 0 = 1`. Public power-sum generators have positive indices.
- Use weighted degree, assigning degree `n` to the generator `e n`. Ordinary polynomial degree in the generators is not symmetric-function degree.
- Reuse Mathlib's `Nat.Partition n`. Do not import a replacement definition with the same name. An unsized adapter may use `Σ n, Nat.Partition n`.
- Ring and Hopf results target arbitrary commutative coefficient rings. The universal special lambda-ring theorem is integral, with arbitrary special lambda-ring targets, including targets with torsion.
- Symmetric functions have bounded degree. Completed symmetric series are a separate type and milestone.
- Preserve all quantifiers, coefficient assumptions, degree bounds, and target structures in an accepted task. If a contract is false or needs revision, document the obstruction and proposed replacement before changing downstream statements. Resolve ordinary proof and API choices autonomously.

## Work units

1. Select a task whose prerequisites are complete. A coordinator or single worker records ownership in the registry; do not have multiple workers edit that file concurrently.
2. Write its precise Lean declarations and a mathematical explanation using `docs/TASK_TEMPLATE.md`. Review the statement, including its referenced definitions, before a long proof search.
3. Search the pinned Mathlib and existing project declarations before introducing new infrastructure. Use Lean MCP diagnostics and goals if available; use `lake env lean` as the compiler fallback.
4. Keep edits within the assigned module scope. Coordinate changes to shared definitions. If multiple agents are explicitly assigned, use separate branches/worktrees and integrate prerequisites before dependents. This document does not itself request spawning agents.
5. Leave a handoff with exported declarations, commands and results, remaining obligations, useful failed approaches, and the commit or exact source state checked. Use `docs/handoffs/<TASK_ID>.md` when implementation begins.

## Proof acceptance

- No `sorry`, `admit`, custom proof axioms, or fabricated instances in accepted library code or its project dependencies. Scratch statements may have holes only outside the accepted library import graph and must never be reported as proved.
- Inspect transitive axioms of milestone declarations. Ordinary Lean foundations such as `propext`, `Classical.choice`, and `Quot.sound` are acceptable; `sorryAx` and new project assumptions are not. Any other axiom dependency requires explicit review rather than silent acceptance.
- Use proof-producing tactics. Avoid `native_decide` in the initial trusted proof path; use kernel-rechecked alternatives.
- Prove equality through public extensionality and generator lemmas. Avoid unfolding the internal representation across the whole project.
- Use targeted imports, scoped notation, and intentional simplification lemmas. Keep private helper lemmas private when appropriate.
- Compile the changed modules and their affected dependents. Integration CI must build every accepted module, including files absent from a root import, and check the root import is current. No unimported-file loophole.
- A successful build with placeholder warnings is not completion. Neither a natural-language argument nor an external platform's accepted reduction is a finished local theorem.
- Add meaningful examples that exercise hypotheses and conventions. Do not count examples as general proofs or require redundant tests of each tactic.
- Mark a task `done` only after its acceptance criteria, statement review, clean proof dependency check, and integration build pass.

## Reuse and external systems

- Keep `/home/ghseeli/SymmetricFun` and `/home/ghseeli/flagged-llt-polynomials` unchanged during normal work here. Port selected results with provenance and attribution; resolve redistribution licensing before copying new colleague code into a distributable project.
- Pin Lean and Mathlib explicitly. Never update dependencies merely to make a proof succeed without recording and validating the environment change.
- Prove2Me is optional. The planning request does not authorize account creation, uploads, publication, or messaging other people. If later authorized, preserve exact statements and environment metadata and recheck imported proofs locally.
- Do not install every suggested tool. Follow the staged infrastructure plan and report genuine setup failures accurately.
