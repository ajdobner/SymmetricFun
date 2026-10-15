# Environment setup

- Task: ENV
- Status: done
- Base commit: `98938de95a12b3ed363653cb980588e2a9188cb8`
- Branch: `codex/symmetric-functions-foundation`
- Fork: https://github.com/ghseeli/SymmetricFun
- Upstream: https://github.com/ajdobner/SymmetricFun
- Local checkout: `/home/ghseeli/lean-sf/SymmetricFun`
- Lean: `leanprover/lean4:v4.34.1`
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612` (release v4.34.1)
- MCP: `lean-lsp-mcp 0.30.0`

## Scope and result

Created a checkout retaining the colleague's full Git history, made the foundation branch, created the user's GitHub fork, and configured origin/upstream. The original `/home/ghseeli/SymmetricFun` remains unchanged. The roadmap, registry, and agent instructions now live in this fork.

The existing `SymmetricPoly` source is retained as inherited draft material. The default accepted library is `SymmetricFunctions`; it currently contains only environment probes. No API, basis, Hopf, or lambda milestone is claimed complete. The original README is preserved in `docs/UPSTREAM_README.md`.

The Lake package name remains `SymmetricPoly` for continuity with upstream. The default library target is `SymmetricFunctions`. The regenerated manifest matches the package name and pins all dependency revisions. New project code uses `autoImplicit = false`; the Mathlib header-license linter is disabled until repository licensing is settled, while other standard linters remain enabled.

## Compatibility evidence

`SymmetricFunctions/Environment.lean` compiles examples using the finite elementary algebra equivalence, weighted graded algebra, elementary specialization, and Hopf antipode. The Hopf probe avoids a redundant Algebra instance because HopfAlgebra already supplies it.

The original `SymmetricPoly/SymmFunc/Basic.lean` was checked separately with its original implicit-variable convention. It has its two known proof holes and one compatibility error in the weighted monomial basis helper. A scratch copy of that helper compiles after replacing `Finsupp.supportedEquivFinsupp` with `AddMonoidAlgebra.supportedEquivFinsupp`. Preserve this adaptation in the later EBASIS port. The scratch probe is not part of the accepted library and the inherited file is unchanged.

The entire inherited power-series/fusion development has not been ported or certified. Its outstanding obligations are listed in the reuse audit. Existing source notices are retained; no new repository license is imposed.

## Validation

- `lake update`: succeeded with network access; installed pinned dependencies and restored 8,907 cache entries.
- `python3 scripts/check_project.py`: succeeded; built both accepted modules and checked transitive axioms of the one named accepted declaration. The unnamed compatibility examples also elaborate in the build.
- `python3 scripts/test_check_project.py`: five tests passed, including omitted-module, nested-comment proof-hole, inherited-draft-import, and dependency-cycle failures.
- `lake env lean .scratch/BadCompilerProbe.lean`: failed as intended on `example : False := by trivial`.
- `lake env lean .scratch/WeightedBasisProbe.lean`: succeeded for the adapted weighted basis helper.
- `bash -n scripts/lean_mcp.sh`: succeeded.
- `git diff --check`: succeeded.

The checker enumerates every accepted source file, requires direct coverage in `SymmetricFunctions.lean`, checks the task graph and evidence for completed tasks, builds all enumerated modules, then runs `scripts/CheckAxioms.lean`. The axiom check inspects declarations by originating module rather than relying on declaration namespace. It accepts only `propext`, `Classical.choice`, and `Quot.sound`. Extend library configuration when introducing the planned `LambdaRing` library; it is already included in the checker's accepted-module prefixes.

## Lean MCP

The project launcher is `scripts/lean_mcp.sh`. It binds the project path and disables optional local Loogle installation and REPL startup. Override `LEAN_MCP_SERVER` for another machine. The installed executable is reused, not reinstalled.

The integration command is:

```sh
timeout 100s /home/ghseeli/.local/share/lean-lsp-mcp-venv/bin/python -u scripts/check_mcp.py
```

Outside the execution sandbox this succeeded: 23 tools discovered, local `esymmAlgEquiv` search returned a result, a valid file returned clean diagnostics, and an invalid proof returned a genuine Lean error. Inside this restricted sandbox the stdio initialization hangs; use the registered MCP host or an approved unsandboxed invocation. The installed Python MCP stack emits a nonfatal subprocess-cleanup warning after the successful check; the process exits zero and the actual diagnostic assertions pass.

Registered a global Codex server named `lean-lsp` using the installed executable with stdio transport, `LEAN_LOOGLE_LOCAL=false`, and `LEAN_REPL=false`. Its configuration was read back successfully. It uses project inference instead of forcing every chat onto this checkout. Future sessions should supply this checkout's path to project-specific tools. This already-running chat is not claimed to have dynamically loaded the new tool catalog.

## Next work

API and PART are ready. The model recommendation is GPT-6 Astra with extra-high effort for foundational design and difficult proofs; GPT-6.1 Sol with high effort is a lower-cost option for bounded implementation tasks. This is a workload recommendation, not a Lean-specific benchmark result. No model setting was changed automatically.

Official references: [model selection](https://developers.openai.com/api/docs/guides/model-selection), [Astra](https://developers.openai.com/api/docs/models/gpt-6-astra), and [Codex MCP configuration](https://learn.chatgpt.com/docs/extend/mcp?surface=cli).

Lean Blueprint and Prove2Me are not installed or activated. No theorem was uploaded to an external proving service.
