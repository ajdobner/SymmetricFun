# Infrastructure for agent proof work

Start with a pinned Lean project, fast compiler feedback, explicit task contracts, and strict integration checks. Add a rendered mathematical blueprint and external proof coordination once stable definitions exist. Recommendations and external documentation were reviewed on 2026-10-14. ENV has now installed the pinned dependencies, configured CI, and verified Lean MCP; see handoffs/ENV.md. Blueprint and Prove2Me remain optional future work.

## Local proof workflow

Use Lean LSP MCP for goals, diagnostics, declaration search, and short proof experiments. The installed entry point is `/home/ghseeli/.local/share/lean-lsp-mcp-venv/bin/lean-lsp-mcp`. The MCP integration test passes outside the restricted execution sandbox: tool discovery, local search, clean diagnostics, and rejection of an invalid proof. The sandboxed stdio probe hangs. A global `lean-lsp` entry is registered in Codex for future sessions, with project inference enabled. `scripts/lean_mcp.sh` is a project-bound launcher for other clients.

After creating a valid Lake project, bind the server to its absolute project path. Verify tool discovery, one local declaration search, and diagnostics for both a correct file and an intentional type error in scratch. Prefer one proof session per worktree; avoid concurrently mutating a shared Lean file through multiple sessions. Keep a compiler CLI fallback. Project-path and transport behavior are documented in the [Lean LSP MCP README](https://github.com/oOo0oOo/lean-lsp-mcp).

For each proof: inspect the goal, search the pinned library, try a small change, inspect diagnostics, and compile the module when it is complete. Do not repeatedly run a whole-library build for each tactic change. Record failing statements and diagnostics in the handoff so another agent can resume without repeating exploration.

## Environment and build coverage

Commit `lean-toolchain`, `lakefile.toml`, and the resolved `lake-manifest.json` together. Set `autoImplicit` to false for new project files. Use the Mathlib binary cache for the selected revision. A fresh environment must compile small imports of the finite symmetric-polynomial, weighted-grading, tensor-product, and Hopf APIs before substantial porting starts.

The fork now pins Lean 4.34.1 and Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`. The colleague's Lean 4.30.0 environment remains the reproduction baseline. The local Mathlib checkout inspected earlier uses 4.33.0-rc2. Prove2Me's documentation currently lists a 4.33.1 environment as default and a 4.30.0 environment as available, but its authenticated environment endpoint is authoritative. If Prove2Me use is pursued, select a compatible supported pin after a port smoke test; otherwise select a suitable stable Mathlib release. Do not choose the release candidate merely because its artifacts are already local. See the platform's [environment documentation](https://github.com/prove2me/prove2me_workspace/blob/main/references/prove.md).

Once ENV has created the package, the normal commands are `lake exe cache get`, `lake build`, and `lake env lean <changed-file>`. ENV must confirm which library targets cover all files on its Lake version and record the exact all-module check. These commands now work in the fork checkout. Use `python3 scripts/check_project.py` for the complete accepted-library check.

Configure CI to:

1. Restore dependencies at the committed pin and build all accepted library modules, not merely an empty root module. Check that the root import lists the intended library surface.
2. Run a no-placeholder scan and inspect transitive axiom dependencies of milestone exports. A text scan is a fast precheck, not the complete trust check.
3. Build a small examples module exercising conventions and integration.
4. Validate task IDs, prerequisites, statuses, and acyclicity; require evidence links for completed tasks.
5. Run an occasional clean-cache build after environment changes. Ordinary proof edits can use incremental builds.

The ENV checks are implemented; extend the milestone audits during RELEASE. A diagram or status badge must not become the source of proof status.

## Task coordination and blueprint

`tasks.json` is the initial dependency registry. ENV is complete; the mathematical tasks remain planned. The coordinator claims ready tasks, records ownership, and serializes status changes; proof workers own specific modules and return handoffs. The registry records scheduling dependencies. The actual Lean import and theorem dependencies remain authoritative about what a proof uses.

Split a large task into child tasks once its formal statements are clear. A good leaf has a fixed statement, known imports, a short proof strategy, and a bounded file scope. Large tasks such as LSPECIAL are research milestones, not single unattended proof prompts.

Use separate worktrees when workers actually run concurrently. Share downloaded immutable dependency artifacts if the tooling supports it, but do not share mutable project build outputs. Integrate in dependency order and recompile consumers after shared interfaces change. Keep failed approaches in task handoffs rather than leaving many incomplete alternatives in the library.

Add [Lean Blueprint](https://github.com/PatrickMassot/leanblueprint) when LPOLY and the lambda proof decomposition are ready for sustained work. It connects mathematical exposition to formal declarations and a dependency graph. Keep the prose proofs, exact conventions, and declaration links there; generate progress from the same task/declaration mapping instead of manually maintaining competing dashboards. Initially, this roadmap and the handoffs are enough.

## Prove2Me assessment

Prove2Me offers theorem cards, checked submissions, and proof decompositions; a solution is checked against the target type. These capabilities are useful for distributing stable lemmas, but do not establish that the target faithfully expresses our intended mathematics. See its [overview](https://prove2.me/about).

Recommended project policy: the local repository owns the definitions and accepted proofs. Use Prove2Me as an optional coordination and verification service once the exported interfaces are stable. Start with one small leaf and evaluate whether its turnaround and integration cost help this project. Do not promise autonomous completion of the lambda theorem from platform availability.

The platform associates declarations with pinned environments. It accepts reductions using other theorem cards, which may still be open. A checked reduction is therefore not necessarily a closed proof. Our acceptance condition is a locally compiling proof with every dependency closed and the same formal statement. See the [proof and reduction documentation](https://github.com/prove2me/prove2me_workspace/blob/main/references/prove.md).

If external work is later authorized, use this pilot:

1. Choose a stable helper, such as partition multiplicity reconstruction or a finite elementary truncation lemma, after the relevant interface task is complete. Review its exact statement locally.
2. Select an explicit supported environment. Export only the required definitions with a reversible local-to-platform declaration mapping. Keep source hashes and dependency IDs.
3. Submit the lemma and an exact-type proof or useful reduction. Keep any placeholder reference modules outside the production library.
4. Retrieve the proof and all dependencies, translate import names if necessary, and compile under the repository pin. Record both platform status and local acceptance.
5. Expand to selected tasks only if the pilot demonstrates useful reuse and manageable environment alignment.

Mission milestones and the open proof frontier are distinct: milestones express curated targets, while proof reductions connect the actual dependency graph. Track both if using a mission. The platform documents [missions and frontier queries](https://github.com/prove2me/prove2me_workspace/blob/main/references/missions.md).

A later mission could expose the integral freeness theorem as its root, with stable realization and Hopf structure as explicit additional milestones. Require RELEASE's local conjunction of all initial targets; proving a platform root alone must not silently omit the Hopf deliverable. Definitions and statements should receive an independent mathematical read-back before launch. The current platform workflow reserves self-audit and proposal submission for the human user; see [mission management](https://github.com/prove2me/prove2me_workspace/blob/main/references/mission_captain.md). No account, proposal, upload, or publication is part of the current planning task.

The supplied [full-project upload workflow](https://github.com/prove2me/prove2me_workspace/blob/main/references/upload_full_project.md) is relevant once a project is already proved and compiling. Our colleague's current checkout has incomplete proofs and conflicting partition models, so an initial wholesale upload is not the proposed integration route.

## Suggested installation order

| When | Infrastructure | Success condition |
| --- | --- | --- |
| ENV | Pinned Lean and Mathlib, cache, Lean MCP or CLI fallback, all-module CI | Fresh checkout builds; intentional scratch error is reported |
| API through FINITE | Task handoffs and declaration review | Stable interfaces and reproducible local proof checks |
| LPOLY decomposition | Lean Blueprint | Mathematical dependencies and Lean declarations are linked |
| After a stable leaf and explicit external-work request | Prove2Me pilot | Exact statement survives export, verification, and local reimport |
| Before RELEASE | Documentation generation and milestone axiom audit | Every claimed theorem is navigable and has closed proof dependencies |

Specialized provers can be considered later for difficult fixed leaves. Adding another prover before fixing statements, imports, and ownership is unlikely to address this project's main early bottlenecks.
