#!/usr/bin/env python3
"""Retain SP-13 eligibility evidence and hashes without unrelated full texts."""
import argparse
import hashlib
import json
from pathlib import Path


def sanitize(raw_bytes):
    record = json.loads(raw_bytes)
    record["complete_private_snapshot_sha256"] = hashlib.sha256(raw_bytes).hexdigest()
    record["retention"] = (
        "All fetched text and matching discussion bodies were read privately. "
        "This public record retains their hashes, lengths, target excerpts, "
        "branch statuses and file inventories; unrelated full texts are omitted."
    )
    cleaned = {}
    for sha, text in record["contents"].items():
        lines = text.splitlines()
        relevant = set()
        for index, line in enumerate(lines):
            if "SP-13" in line:
                relevant.update(range(max(0, index - 1), min(len(lines), index + 2)))
        cleaned[sha] = {
            "bytes": len(text.encode()),
            "sha256": hashlib.sha256(text.encode()).hexdigest(),
            "target_excerpts": [lines[index] for index in sorted(relevant)],
        }
    record["contents"] = cleaned
    for entry in record["discussion_matches"]:
        body = entry.pop("body", None) or ""
        entry["body_bytes"] = len(body.encode())
        entry["body_sha256"] = hashlib.sha256(body.encode()).hexdigest()
        entry["target_excerpts"] = [line for line in body.splitlines() if "SP-13" in line]
        entry["assessment_required"] = (
            "The complete body requires manual review. Excerpts alone do not "
            "establish mathematical status; the dated submission record gives "
            "the assessment for its recorded snapshot."
        )
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = sanitize(args.input.read_bytes())
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(hashlib.sha256(args.output.read_bytes()).hexdigest(), args.output)


if __name__ == "__main__":
    main()
