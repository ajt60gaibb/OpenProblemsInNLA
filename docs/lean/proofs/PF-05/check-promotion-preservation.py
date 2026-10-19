#!/usr/bin/env python3
"""Check intentional PF05 status promotion while preserving IDs and originals."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess

REPO = Path(__file__).resolve().parents[4]
BASE = "235984a1515b3dc8d22712bd7fb7bb26d5f70487"
EVIDENCE = Path(__file__).with_name("promotion")
ARCHIVE = Path(__file__).with_name("originals-main-36767")
CANONICAL = "nonnegative-and-positive-factorizations/PF-05/README.md"
PROJECT = "nonnegative-and-positive-factorizations/PF-05/lean"
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--base-ref", default=BASE)
parser.add_argument("--output", type=Path, default=EVIDENCE / "preservation.json")
parser.add_argument("--ci-result", type=Path, required=True)
args = parser.parse_args()
BASE = subprocess.check_output(["git", "rev-parse", args.base_ref], cwd=REPO, text=True).strip()
checks = []


def sha(data):
    return hashlib.sha256(data).hexdigest()


def original(path):
    return subprocess.check_output(["git", "show", BASE + ":" + path], cwd=REPO)


def check(name, passed, **data):
    checks.append({"name": name, "passed": bool(passed), **data})


registry_bytes = original("problem_ids.json")
registry = json.loads(registry_bytes)
current_registry = (REPO / "problem_ids.json").read_bytes()
check("registry-byte-identity", current_registry == registry_bytes, ids=len(registry))
check("registry-ID-path-mappings", json.loads(current_registry) == registry)
check("all-canonical-paths-retained", all((REPO / p).is_file() for p in registry.values()))
pages = []
for problem_id, name in sorted(registry.items()):
    base, actual = original(name), (REPO / name).read_bytes()
    pages.append({"id": problem_id, "path": name, "base_sha256": sha(base),
                  "current_sha256": sha(actual), "unchanged": actual == base})
changed_pages = [p["id"] for p in pages if not p["unchanged"]]
check("only-PF05-canonical-page-changes", changed_pages == ["PF-05"], changed_ids=changed_pages)
base_readme = original(CANONICAL).decode()
new_readme = (REPO / CANONICAL).read_text()
pattern = r"<!-- formal-lean-proof:start -->.*?<!-- formal-lean-proof:end -->\n\n"
stripped, count = re.subn(pattern, "", new_readme, flags=re.S)
stripped = stripped.replace("**Status:** Lean verified", "**Status:** Solved", 1)
stripped = stripped.replace("**Last checked:** 2026-10-18", "**Last checked:** 2026-09-11", 1)
check("all-original-PF05-text-credits-history-retained", count == 1 and stripped == base_readme)
check("PF05-status-Lean-verified", re.search(r"^\*\*Status:\*\* Lean verified[ \t]*$", new_readme, re.M) is not None)
manifest = json.loads((ARCHIVE / "manifest.json").read_text())
for item in manifest["records"]:
    data = (REPO / item["archive"]).read_bytes()
    check("original-archive:" + item["source"], data == original(item["source"])
          and sha(data) == item["sha256"], sha256=sha(data))

tracked = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", "-z", BASE], cwd=REPO).decode().split("\0")
artifacts = []
for problem_id, canonical in sorted(registry.items()):
    parent = PurePosixPath(canonical).parent
    for name in tracked:
        if name and PurePosixPath(name).parent == parent and name != canonical:
            old = original(name)
            file = REPO / name
            actual = file.read_bytes() if file.is_file() else b""
            artifacts.append({"id": problem_id, "path": name, "base_sha256": sha(old),
                              "current_sha256": sha(actual), "unchanged": old == actual})
changed_artifacts = [a["path"] for a in artifacts if not a["unchanged"]]
expected = ["nonnegative-and-positive-factorizations/PF-05/problem.pdf", "nonnegative-and-positive-factorizations/PF-05/problem.tex"]
check("only-authorized-regenerated-artifacts-change", sorted(changed_artifacts) == expected,
      original_artifacts=len(artifacts), unchanged_original_artifacts=sum(a["unchanged"] for a in artifacts),
      regenerated=changed_artifacts)

def tex_target(text):
    return text.split(r"\subsection{Problem statement}", 1)[1].split(r"\subsection{Reference and status}", 1)[0]

def normalized_tex_target(text):
    # Current repository rendering preserves the exact original Markdown but
    # emits mathop/nolimits rather than operatorname for these two operators.
    for name in ["rank", "tr"]:
        text = text.replace(r"\mathop{\mathrm{" + name + r"}}\nolimits", r"\operatorname{" + name + "}")
    return re.sub(r"\s+", "", tex_target(text).replace(r"\newpage", ""))


check("generated-TeX-target-equal-modulo-spacing-and-standard-operator-notation",
      normalized_tex_target((ARCHIVE / "problem.tex").read_text()) ==
      normalized_tex_target((REPO / "nonnegative-and-positive-factorizations/PF-05/problem.tex").read_text()))
for name in ["NLA/Statements/PF05.lean", "NLA/Statements/Infrastructure.lean", "Reviewed/PF05.lean"]:
    base = original("lean-statements/" + name)
    check("frozen-boundary:" + name, (REPO / PROJECT / name).read_bytes() == base,
          sha256=sha(base))
ci = json.loads(args.ci_result.read_text())
lean_inputs = {name: h for name, h in ci["input_sha256"].items() if name.endswith(".lean")}
check("all-checked-Lean-proof-statement-inputs-unchanged", all(sha((REPO / PROJECT / name).read_bytes()) == h
      for name, h in lean_inputs.items()), lean_source_count=len(lean_inputs), checked_commit=ci["repository_commit"])
check("repository-render-succeeded-without-warnings", (EVIDENCE / "render.log").read_text().strip() ==
      "PF-05: OK\nRendered 1 problem documents.")
result = {"checked_on": "2026-10-18", "reviewer": "reproducible preservation checker (/root, Codex AI agent)",
          "scope": "Intentional PF05 status/evidence promotion, permanent-ID/path preservation, exact original archives and unchanged target/proof sources",
          "base_ref": BASE, "checks": checks, "pages": pages, "original_artifacts": artifacts,
          "passed": all(c["passed"] for c in checks),
          "note": "Historical all-828 byte-preservation report remains unchanged. This separate report allows only the documented PF05 notice/status and two regenerated artifacts, with all five exact originals archived before edits."}
args.output.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"passed": result["passed"], "checks": len(checks),
                  "failed_checks": [c["name"] for c in checks if not c["passed"]]}, indent=2))
raise SystemExit(0 if result["passed"] else 1)
