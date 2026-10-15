#!/usr/bin/env python3
"""Check the accepted library, task DAG, build coverage, and transitive axioms."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ACCEPTED = ("SymmetricFunctions", "LambdaRing")


def lean_code(text: str) -> str:
    """Remove nested comments and strings for the fast lexical precheck."""
    out = []
    i = depth = 0
    string = False
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif string:
            if text[i] == "\\":
                i += 2
            elif text[i] == '"':
                string = False
                i += 1
            else:
                i += 1
        elif pair == "/-":
            depth = 1
            out.append(" ")
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            string = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def validate(root: Path) -> list[str]:
    data = json.loads((root / "docs/tasks.json").read_text())
    tasks = {t["id"]: t for t in data["tasks"]}
    if len(tasks) != len(data["tasks"]):
        raise ValueError("Duplicate task IDs")
    visiting, done = set(), set()

    def visit(name: str) -> None:
        if name not in tasks:
            raise ValueError(f"Unknown prerequisite: {name}")
        if name in visiting:
            raise ValueError(f"Task dependency cycle: {name}")
        if name in done:
            return
        visiting.add(name)
        task = tasks[name]
        if task["status"] not in {"planned", "in_progress", "review", "blocked", "done"}:
            raise ValueError(f"Invalid status: {name}")
        for dep in task["depends_on"]:
            visit(dep)
        if task["status"] == "done":
            if any(tasks[d]["status"] != "done" for d in task["depends_on"]):
                raise ValueError(f"Completed task has unfinished prerequisites: {name}")
            evidence = task.get("evidence")
            if not evidence or not (root / evidence).is_file():
                raise ValueError(f"Missing completion evidence: {name}")
        visiting.remove(name)
        done.add(name)

    for name in tasks:
        visit(name)

    files = [root / "SymmetricFunctions.lean"]
    for directory in ACCEPTED:
        files.extend(sorted((root / directory).rglob("*.lean")))
        if directory != "SymmetricFunctions" and (root / f"{directory}.lean").exists():
            files.append(root / f"{directory}.lean")
    modules = {str(p.relative_to(root).with_suffix("")).replace("/", "."): p for p in files}
    if len(modules) < 2:
        raise ValueError("Accepted library has no modules")
    imports = {}
    for name, path in modules.items():
        code = lean_code(path.read_text())
        bad = re.search(r"\b(sorry|admit|axiom|native_decide|sorryAx)\b", code)
        if bad:
            raise ValueError(f"Forbidden proof token {bad[0]} in {path.relative_to(root)}")
        imports[name] = re.findall(r"(?m)^\s*(?:public\s+)?(?:meta\s+)?import\s+([\w.]+)", code)
        for dependency in imports[name]:
            if dependency.startswith("SymmetricPoly"):
                raise ValueError(f"Accepted module {name} imports inherited draft {dependency}")
    root_imports = set(imports["SymmetricFunctions"])
    missing = set(modules) - {"SymmetricFunctions"} - root_imports
    if missing:
        raise ValueError(f"Root import does not cover: {', '.join(sorted(missing))}")
    print(f"Static checks passed: {len(tasks)} tasks, {len(modules)} accepted modules.", flush=True)
    return sorted(modules)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--static-only", action="store_true")
    args = parser.parse_args()
    try:
        modules = validate(ROOT)
        if not args.static_only:
            subprocess.run(["lake", "build", *modules], cwd=ROOT, check=True)
            subprocess.run(["lake", "env", "lean", "scripts/CheckAxioms.lean"], cwd=ROOT, check=True)
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        print(f"Project check failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
