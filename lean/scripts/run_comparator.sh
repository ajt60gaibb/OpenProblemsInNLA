#!/usr/bin/env bash
set -euo pipefail

LEAN_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORKSPACE_ROOT="$(cd "$LEAN_ROOT/.." && pwd)"

resolve_tool() {
  local env_name="$1"
  local default_name="$2"
  local value="${!env_name:-}"

  if [[ -n "$value" ]]; then
    if [[ ! -x "$value" ]]; then
      echo "$env_name is not an executable file: $value" >&2
      exit 2
    fi
    (cd "$(dirname "$value")" && printf '%s/%s\n' "$PWD" "$(basename "$value")")
    return
  fi

  if ! command -v "$default_name" >/dev/null 2>&1; then
    echo "Missing $default_name. Set $env_name to its absolute executable path." >&2
    exit 2
  fi
  command -v "$default_name"
}

for tool in lake tar systemd-run; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "Missing required command: $tool" >&2
    exit 2
  fi
done

if [[ "$(id -u)" -eq 0 ]]; then
  echo "Comparator must not be run as root. Use a non-root Linux user." >&2
  exit 2
fi

COMPARATOR_BIN_RESOLVED="$(resolve_tool COMPARATOR_BIN comparator)"
LANDRUN_BIN_RESOLVED="$(resolve_tool COMPARATOR_LANDRUN landrun)"
LEAN4EXPORT_BIN_RESOLVED="$(resolve_tool COMPARATOR_LEAN4EXPORT lean4export)"

if [[ ! -d "$WORKSPACE_ROOT/proof" ]]; then
  echo "Missing sibling source folder: $WORKSPACE_ROOT/proof" >&2
  exit 2
fi

if [[ ! -f "$LEAN_ROOT/lake-manifest.json" ]]; then
  echo "lake-manifest.json is missing. Run lake update during statement setup first." >&2
  exit 2
fi

TMP="$(mktemp -d -t lean-proof-comparator.XXXXXX)"
cleanup() {
  rm -rf "$TMP"
}
trap cleanup EXIT INT TERM

WORKSPACE="$TMP/project"
mkdir -p "$WORKSPACE"

# Copy the whole project workspace so source-data references such as
# ../proof/<path> remain valid. Never reuse the development Lean
# environment or Git metadata.
tar -C "$WORKSPACE_ROOT" \
  --exclude='./.git' \
  --exclude='*/.git' \
  --exclude='./lean/.lake' \
  --exclude='./lean/.tools' \
  --exclude='./lean/.verification-tmp' \
  -cf - . | tar -C "$WORKSPACE" -xf -

LEAN_WORK="$WORKSPACE/lean"
if [[ ! -f "$LEAN_WORK/lakefile.toml" ]]; then
  echo "Fresh copy is missing lean/lakefile.toml" >&2
  exit 2
fi

cd "$LEAN_WORK"

# Materialize the pinned dependency graph without compiling Solution. Mathlib's
# trusted cache substantially reduces the checking cost when available.
lake update
if [[ "${SKIP_MATHLIB_CACHE:-0}" != "1" ]]; then
  lake exe cache get || {
    echo "Mathlib cache retrieval was unavailable; continuing with a source build." >&2
  }
fi

export COMPARATOR_BIN="$COMPARATOR_BIN_RESOLVED"
export COMPARATOR_LANDRUN="$LANDRUN_BIN_RESOLVED"
export COMPARATOR_LEAN4EXPORT="$LEAN4EXPORT_BIN_RESOLVED"
export COMPARATOR_CONFIG="$LEAN_WORK/comparator.json"

systemd-run \
  --property=RestrictAddressFamilies=~AF_UNIX \
  --user \
  --pty \
  --wait \
  --collect \
  -E PATH="$PATH" \
  -E COMPARATOR_BIN="$COMPARATOR_BIN" \
  -E COMPARATOR_LANDRUN="$COMPARATOR_LANDRUN" \
  -E COMPARATOR_LEAN4EXPORT="$COMPARATOR_LEAN4EXPORT" \
  -E COMPARATOR_CONFIG="$COMPARATOR_CONFIG" \
  --working-directory "$LEAN_WORK" \
  -- bash -lc 'lake env "$COMPARATOR_BIN" "$COMPARATOR_CONFIG"'
