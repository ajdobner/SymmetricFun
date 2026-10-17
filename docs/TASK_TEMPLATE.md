# Implementation task handoff

Copy this template to `docs/handoffs/<TASK_ID>.md` when claiming an implementation task. Update the existing handoff when resuming it. Paths below are repository-relative unless identified as external sources.

- Task ID and owner:
- Status: planned / in_progress / review / blocked / done
- Prerequisite tasks and checked commits:
- Lean toolchain and full Mathlib revision:
- Assigned files:
- Reference sources and attribution:

## Mathematical contract

State the theorem with all quantifiers, coefficient assumptions, index conventions, bounds, and normalizations. Explain the definitions it depends on and why it advances the named milestone.

## Formal interface

Record exact Lean declaration names, statements, imports, and required definitions after they elaborate. Before that, label signatures as proposed. Keep placeholder Lean files outside the accepted library. Record a source commit or content hash so later statement changes are visible.

## Statement review

Translate the Lean declaration back into mathematics, including implicit hypotheses and instances. For a major milestone, have a separate review pass without first showing the intended proof. Check zero degree, empty alphabets, arbitrary coefficient rings where promised, and whether hypotheses accidentally assume the conclusion. Record reviewer and any corrections. Review need not involve a new agent unless delegation is authorized.

## Proof strategy

List the intermediate claims and available lemmas. Identify the hardest obligation explicitly. Record failed approaches only when they will prevent repeated work. For a failed approach, include the actual goal or diagnostic and why it failed.

## Validation and integration

- Exact commands and exit results:
- Modules checked, including affected dependents:
- Exported declaration axiom audit:
- Convention or edge-case examples:
- Root import coverage and integration result:
- Remaining gaps:

## Optional external proof mapping

Only if external use has been authorized: platform theorem/definition IDs, environment, local names, exact statement/source hashes, uploaded dependencies, and proof or reduction status. Record whether every reduction leaf is closed and the returned proof compiles locally.

## Completion

Link the final source state and state which acceptance criteria passed. A draft statement, proof sketch, or partially closed dependency graph remains unfinished.
