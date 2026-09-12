#!/usr/bin/env python3
"""Verify this recorded merge without rebuilding or changing any artifact.

Run inside a clone containing both recorded parent commits. This is a dated
integration check, not a claim about later edits or a mathematical proof check.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def main():
    here = Path(__file__).resolve().parent
    root = here.parents[2]
    record = json.loads((here / "main-integration-2026-09-11-87366c6.json").read_text())
    prior = record["prior_head"]
    incoming = record["incoming_commit"]
    reference_readme = record["reference_directory"] + "/README.md"

    def git(*args):
        return subprocess.check_output(["git", "-C", str(root), *args])

    def old(commit, path):
        return git("show", commit + ":" + path)

    protected = 0
    for path, expected in record["original_proof_and_reference_hashes"].items():
        data = (root / path).read_bytes()
        if path == reference_readme:
            prefix = old(prior, path)
            assert sha256(prefix) == expected["sha256"], path + ": original hash"
            assert len(prefix) == expected["bytes"], path + ": original size"
            assert data.startswith(prefix), path + ": historical text changed"
            assert data[len(prefix):].startswith(
                b"\n## Integration with accepted main"), path + ": unexpected append"
        else:
            assert sha256(data) == expected["sha256"], path + ": protected hash"
            assert len(data) == expected["bytes"], path + ": protected size"
            protected += 1

    for path, expected in record["current_files"].items():
        data = (root / path).read_bytes()
        assert sha256(data) == expected["sha256"], path + ": integration hash"
        assert len(data) == expected["bytes"], path + ": integration size"

    registry_bytes = (root / "problem_ids.json").read_bytes()
    assert registry_bytes == old(prior, "problem_ids.json")
    assert registry_bytes == old(incoming, "problem_ids.json")
    registry = json.loads(registry_bytes)
    assert len(registry) == 203
    owned = set(record["owned_ids"])
    incoming_pages = 0
    for ident, path in registry.items():
        data = (root / path).read_bytes()
        if ident not in owned:
            assert data == old(incoming, path), ident + ": incoming canonical page"
            incoming_pages += 1
        elif ident == "AA-01":
            marker = b"## Problem statement\n"
            previous = old(prior, path)
            assert data[data.index(marker):] == previous[previous.index(marker):], "AA-01: original target/source text"
            start, end = b"<!-- colbrook-arithmetic -->", b"<!-- /colbrook-arithmetic -->"
            accepted = old(incoming, path)
            block = accepted[accepted.index(start):accepted.index(end) + len(end)]
            assert block in data, "AA-01: accepted Colbrook notice"
            assert b"Separate reviewed proof by George Stepaniants" in data
        else:
            assert data == old(prior, path), ident + ": owned canonical page"
    assert incoming_pages == record["upstream_canonical_pages_byte_identical"]

    evidence = 0
    for item in git("ls-tree", "-r", "-z", incoming).split(b"\0"):
        if not item:
            continue
        meta, path_bytes = item.split(b"\t", 1)
        path = path_bytes.decode()
        if path.startswith("references/") or re.search(r"/solution\.(md|tex|pdf)$", path):
            data = (root / path).read_bytes()
            actual = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
            expected = meta.split()[2].decode()
            assert actual == expected, path + ": incoming evidence changed"
            evidence += 1
    assert evidence == record["upstream_proof_and_evidence_blobs_byte_identical"]

    for path in (root / reference_readme, here / "main-integration-2026-09-11-87366c6.md"):
        for target in re.findall(r"\]\(([^)]+)\)", path.read_text()):
            target = target.split("#", 1)[0]
            if target and not re.match(r"(?:https?:|mailto:|#)", target):
                assert (path.parent / target).exists(), str(path) + ": missing " + target

    print("PASS:", ", ".join(sorted(owned)), "—", protected,
          "unchanged reviewed artifacts; original reference README retained;",
          incoming_pages, "incoming canonical pages;", evidence,
          "incoming proof/evidence blobs; 203 permanent IDs; current fingerprints.")


if __name__ == "__main__":
    main()
