# Symmetric functions in Lean

This fork of [ajdobner/SymmetricFun](https://github.com/ajdobner/SymmetricFun) develops the integral ring of symmetric functions, its stable polynomial realization, Hopf algebra structure, and universal special lambda-ring property. The polynomial-backed design is fixed in the [roadmap](docs/ROADMAP.md).

ENV, API, PART, GRADE, EBASIS, BASE, SPEC, COMPLETE, OMEGA, HBASIS, FINITE, STABLE, NEWTON, HOPF, LPOLY, LDEFS, LLINE, LSPECIAL, LSTABLE, LFREE, and RELEASE are complete. The default `SymmetricFunctions` library provides the polynomial-backed public type, elementary generators, universal algebra evaluation, and the equivalence between Mathlib partitions and weighted exponent vectors. Weighted grading, the exhaustive degree filtration, and elementary partition bases are also proved. The bounded stable realization and the standard connected, cocommutative Hopf structure are proved over arbitrary commutative rings. The integral free special lambda-ring theorem is proved for arbitrary special targets, including targets with additive torsion. The initial core release includes a proved nonzero torsion target example, a separate mathematical statement review, and a clean build and axiom audit of all 55 accepted modules. The inherited `SymmetricPoly` files remain drafts and are excluded from the accepted-library build. The [original README](docs/UPSTREAM_README.md) and Git history preserve the colleague's work.

## Build and check

The project pins Lean **v4.34.1** and Mathlib **d13f23b723b8a846827a245b89c10fc7d3f11612**.

```sh
lake exe cache get
python3 scripts/test_check_project.py
python3 scripts/check_project.py
```

The checker validates the task graph, rejects proof holes and draft imports, verifies coverage of every accepted module, builds them, and audits transitive axiom dependencies. It also runs notation scope, type-boundary, and proof-goal display checks. A plain `lake build` builds the default accepted library.

## Start an implementation task

Read [AGENTS.md](AGENTS.md), then select a ready task in [docs/tasks.json](docs/tasks.json). The initial core release is complete. **PLETH has its basic integral operation and laws implemented; Adams and tensor compatibility remain. MONOMIAL is also ready**, outside the completed core scope. Use the [handoff template](docs/TASK_TEMPLATE.md). The [API handoff](docs/handoffs/API.md) records the representation decision and public interface; the [PART handoff](docs/handoffs/PART.md) records the partition adapter. The [ENV handoff](docs/handoffs/ENV.md) records the pinned environment and MCP setup.

## Optional mathematical notation

```lean
import SymmetricFunctions.Notation
open scoped SymmetricFunctionNotation
```

This enables `Λ[R]`, `ω f`, `λ[n] a`, and integral `f⟦g⟧`. Import alone leaves the scope inactive. Existing names remain available, with descriptive aliases for elementary, complete, power-sum functions, and the involution. Uppercase `Ω` is reserved for the future degree completion. See the [notation and alphabet guide](docs/NOTATION.md) for precedence, coefficient roles, and virtual negation versus parameter scaling.

Other references:

- [Declaration guide and generated index](docs/DECLARATIONS.md)
- [Release validation and statement review](docs/handoffs/RELEASE.md)
- [Existing work audit](docs/REUSE_AUDIT.md)
- [Infrastructure and Prove2Me recommendations](docs/INFRASTRUCTURE.md)

## Lean MCP

A project-bound stdio launcher is available at `scripts/lean_mcp.sh`. It uses the installed server on the setup machine; set `LEAN_MCP_SERVER` to your executable elsewhere. Lean MCP 0.30.0 was tested with declaration search and both clean and error diagnostics. The local Codex configuration also registers `lean-lsp` with project inference for future sessions.

The optional `scripts/check_mcp.py` integration test requires Python with the `mcp` package. The setup machine has it in the Lean MCP virtual environment. Restricted sandbox execution may hang during stdio startup; the integration test passed outside that sandbox.

## Model recommendation

Use **GPT-6 Astra / extra high** for foundational choices, the stable-range proofs, and the lambda universal-property work. **GPT-6.1 Sol / high** is a lower-cost option for bounded lemmas, porting, and routine maintenance. Review exact statements and require compiler evidence regardless of model. This recommendation follows the workload distinctions in [OpenAI's model-selection guidance](https://developers.openai.com/api/docs/guides/model-selection); it is not a measured Lean benchmark.
