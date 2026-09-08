#!/usr/bin/env python3
"""Block routine integrity hashes except the one-file proof-artifact helper."""

from __future__ import annotations

import json
import re
import sys

DENIAL = (
    "Blocked by the proof project's hash policy. Routine integrity hashes are "
    "forbidden. For one individually named, stable, proof-bearing computer-"
    "assisted artifact, use `.codex/hooks/proof_artifact_hash.py lock|verify "
    "PATH`. Never hash a repository, directory, glob, ordinary bundle, or "
    "general collection, and do not evade this hook."
)

PATTERNS = [
    r"(?i)(?:^|[\s;&|])(?:sha(?:1|224|256|384|512)sum|shasum|md5(?:sum)?|b2sum|b3sum|cksum|crc32|rhash|hashdeep)(?=$|[\s;&|])",
    r"(?i)\bopenssl(?:\.exe)?\s+(?:dgst|md5|sha1|sha224|sha256|sha384|sha512)\b",
    r"(?i)\bcertutil(?:\.exe)?\b[^\n;&|]*\s-hashfile\b",
    r"(?i)\bget-filehash\b",
    r"(?i)\bgit(?:\.exe)?\b[^\n;&|]*\bhash-object\b",
    r"(?is)\b(?:python(?:2|3(?:\.\d+)?)?|py|node(?:js)?|deno|bun)\b[^\n;&|]*(?:hashlib|file_digest|createHash|subtle\.digest)",
]


def main() -> int:
    try:
        payload = json.load(sys.stdin)
    except (json.JSONDecodeError, OSError, TypeError):
        return 0

    tool_input = payload.get("tool_input")
    command = tool_input.get("command") if isinstance(tool_input, dict) else None
    if not isinstance(command, str) or not any(re.search(pattern, command) for pattern in PATTERNS):
        return 0

    print(json.dumps({
        "hookSpecificOutput": {
            "hookEventName": "PreToolUse",
            "permissionDecision": "deny",
            "permissionDecisionReason": DENIAL,
        }
    }))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
