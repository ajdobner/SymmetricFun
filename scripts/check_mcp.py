#!/usr/bin/env python3
"""Optional Lean MCP integration check. Run with a Python environment containing mcp."""
import asyncio
import json
from pathlib import Path

from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

ROOT = Path(__file__).resolve().parents[1]


def payload(result):
    if getattr(result, "is_error", getattr(result, "isError", False)):
        raise RuntimeError(str(result.content))
    return json.loads(next(c.text for c in result.content if c.type == "text"))


async def check():
    scratch = ROOT / ".scratch"
    scratch.mkdir(exist_ok=True)
    good = scratch / "McpGood.lean"
    bad = scratch / "McpBad.lean"
    good.write_text("import SymmetricFunctions\nexample : True := by trivial\n")
    bad.write_text("import SymmetricFunctions\nexample : False := by trivial\n")
    try:
        params = StdioServerParameters(command="bash", args=[str(ROOT / "scripts/lean_mcp.sh")])
        print("Starting Lean MCP...", flush=True)
        async with stdio_client(params) as (reader, writer):
            async with ClientSession(reader, writer) as session:
                await session.initialize()
                names = {t.name for t in (await session.list_tools()).tools}
                assert {"lean_local_search", "lean_diagnostic_messages"} <= names
                print(f"Discovered {len(names)} tools.", flush=True)
                search = payload(await session.call_tool("lean_local_search", {
                    "query": "esymmAlgEquiv", "limit": 3, "project_root": str(ROOT)
                }))
                assert "esymmAlgEquiv" in json.dumps(search), search
                print("Local search passed.", flush=True)
                for file in [good, bad]:
                    result = payload(await session.call_tool("lean_diagnostic_messages", {
                        "file_path": str(file), "timeout_s": 30
                    }))
                    print(f"{file.name}: {json.dumps(result)}", flush=True)
                    assert not result.get("partial", False), result
                    assert not result.get("timed_out", False), result
                    assert not result.get("failed_dependencies"), result
                    # Schema field names vary across MCP server versions.
                    diagnostics = result.get("items", result.get("diagnostics", []))
                    assert not any("diagnostics_unavailable" in d.get("message", "")
                                   for d in diagnostics), result
                    errors = [d for d in diagnostics
                              if d.get("severity") in (1, "error", "Error")]
                    assert bool(errors) == (file == bad), result
                print("Lean MCP search and positive/negative diagnostics passed.", flush=True)
    finally:
        good.unlink(missing_ok=True)
        bad.unlink(missing_ok=True)


async def main():
    async with asyncio.timeout(90):
        await check()


if __name__ == "__main__":
    asyncio.run(main())
