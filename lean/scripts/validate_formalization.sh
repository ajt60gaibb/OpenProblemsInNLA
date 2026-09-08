#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# The upstream dispatcher selects the schema from formalization.yaml's `version`.
SCHEMA="https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/schema/formalization.schema.json"

if ! command -v check-jsonschema >/dev/null 2>&1; then
  cat >&2 <<'EOF'
Missing `check-jsonschema`.
Install it in the verification environment, for example with:
  python -m pip install check-jsonschema
Then rerun this script.
EOF
  exit 2
fi

cd "$ROOT"
check-jsonschema --schemafile "$SCHEMA" formalization.yaml
