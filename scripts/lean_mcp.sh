#!/usr/bin/env bash
set -euo pipefail
PROJECT_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
export LEAN_PROJECT_PATH="$PROJECT_ROOT"
export LEAN_LOOGLE_LOCAL=false
export LEAN_REPL=false
export LEAN_LOG_LEVEL=ERROR
MCP_SERVER="${LEAN_MCP_SERVER:-/home/ghseeli/.local/share/lean-lsp-mcp-venv/bin/lean-lsp-mcp}"
if [[ ! -x "$MCP_SERVER" ]]; then
  MCP_SERVER="$(command -v lean-lsp-mcp || true)"
fi
if [[ -z "$MCP_SERVER" || ! -x "$MCP_SERVER" ]]; then
  echo 'Set LEAN_MCP_SERVER to an installed lean-lsp-mcp executable.' >&2
  exit 1
fi
cd "$PROJECT_ROOT"
exec "$MCP_SERVER" --transport stdio
