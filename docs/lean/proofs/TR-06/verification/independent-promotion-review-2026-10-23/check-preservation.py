#!/usr/bin/env python3
"""Read-only review of the concrete TR06 descriptive promotion; never writes canonical inputs."""
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess

REPO = Path(__file__).resolve().parents[6]
OUT = Path(__file__).resolve().parent
PROOF = "2b049df5e9b15318987f3fa592b1a7c65a0c0057"
ORIGINAL = "c4c7be592c51c8ba81d1579082813310a22b356d"
PUBLISHED = "3da7a876b97815c99ebde0f4f9c17932096345a2"
STATEMENT = "36767fa430309f13d04dc6ebe080d470f5c2444a"
PROJECT = "tensor-computations/TR-06/lean"
CANONICAL = "tensor-computations/TR-06/README.md"
FREEZE = "docs/lean/proofs/TR-06/verification/promotion-before-commit-2026-10-23/source-lock.json"
FREEZE_SHA = "838f29c15e7804416b869c2c4d25bfbed2f5c15b46afdd35e390afbd73b5bcc7"
V = "docs/lean/proofs/TR-06/verification"
checks = []


def digest(data):
    return hashlib.sha256(data).hexdigest()


def current(path):
    return (REPO / path).read_bytes()


def old(path, ref=PROOF):
    return subprocess.check_output(["git", "show", f"{ref}:{path}"], cwd=REPO)


def check(name, passed, **evidence):
    checks.append({"name": name, "passed": bool(passed), **evidence})


freeze_bytes = current(FREEZE)
freeze = json.loads(freeze_bytes)
check("exact-322-input-promotion-freeze", digest(freeze_bytes) == FREEZE_SHA
      and len(freeze["records"]) == 322
      and len({r["path"] for r in freeze["records"]}) == 322
      and all(digest(current(r["path"])) == r["sha256"] for r in freeze["records"]))

registry_bytes = current("problem_ids.json")
registry = json.loads(registry_bytes)
check("all-217-permanent-IDs-and-paths-unchanged", len(registry) == 217
      and registry["TR-06"] == CANONICAL
      and registry_bytes == old("problem_ids.json", ORIGINAL) == old("problem_ids.json"))
other_pages = []
for identifier, path in registry.items():
    if identifier != "TR-06":
        data = current(path)
        other_pages.append({"id": identifier, "path": path, "sha256": digest(data),
                            "passed": data == old(path, ORIGINAL) == old(path)})
check("all-216-other-canonical-pages-byte-exact", len(other_pages) == 216
      and all(r["passed"] for r in other_pages), count=len(other_pages))

readme = current(CANONICAL)
stripped, notice_count = re.subn(
    rb"\n<!-- lean-tr06-complete-2026-10-23 -->\n.*?<!-- /lean-tr06-complete-2026-10-23 -->\n",
    b"", readme, flags=re.S)
stripped = stripped.replace(b"**Status:** Lean verified  \n", b"**Status:** Solved  \n", 1)
stripped = stripped.replace(b"**Last checked:** 2026-10-23  \n", b"**Last checked:** 2026-09-11  \n", 1)
check("strip-only-authorized-notice-status-date-recovers-exact-original-README",
      notice_count == 1 and stripped == old(CANONICAL, ORIGINAL) == old(CANONICAL),
      original_sha256=digest(stripped), current_sha256=digest(readme))

manifest_path = "docs/lean/proofs/TR-06/originals-c4c7be59/manifest.json"
archive_manifest = json.loads(current(manifest_path))
archives = []
for r in archive_manifest["records"]:
    original, archived = old(r["source"], ORIGINAL), current(r["archive"])
    archives.append({**r, "actual_archive_sha256": digest(archived),
                     "passed": digest(original) == r["sha256"] == digest(archived) and original == archived})
check("all-five-original-archives-byte-exact", archive_manifest["base_ref"] == ORIGINAL
      and len(archives) == 5 and all(r["passed"] for r in archives))
check("both-original-submitted-manuscripts-untouched",
      all(current(r["source"]) == old(r["source"], ORIGINAL)
          for r in archive_manifest["records"] if "/manuscripts/" in r["source"]))

actual = json.loads(current(V + "/linux-ci/2b049df5/artifact/verify-20261023T224123Z-3965/result.json"))
proof_inputs = actual["input_sha256"]
unchanged_lean = []
changed_descriptions = []
for path, expected in proof_inputs.items():
    data = current(PROJECT + "/" + path)
    if path.endswith(".lean"):
        unchanged_lean.append({"path": path, "sha256": digest(data),
                               "passed": digest(data) == expected and data == old(PROJECT + "/" + path)})
    elif digest(data) != expected:
        changed_descriptions.append(path)
check("all-144-Lean-inputs-exact-actual-Linux-proof-bytes", len(unchanged_lean) == 144
      and all(r["passed"] for r in unchanged_lean))
check("only-two-descriptive-package-inputs-differ-from-proof-receipt",
      set(changed_descriptions) == {"README.md", "formalization.yaml"}
      and len(proof_inputs) == 153, changed_inputs=changed_descriptions)

copy_lock_bytes = current(PROJECT + "/proof-source-lock.json")
copy_lock = json.loads(copy_lock_bytes)
copies = []
for r in copy_lock["copies"]:
    shared, canonical = current(r["source"]), current(r["destination"])
    copies.append({"source": r["source"], "destination": r["destination"],
                   "sha256": digest(shared), "passed": shared == canonical == old(r["source"])
                   == old(r["destination"]) and digest(shared) == r["source_sha256"] == r["destination_sha256"]})
check("all-140-shared-canonical-copies-and-copy-lock-unchanged", len(copies) == 140
      and all(r["passed"] for r in copies) and copy_lock_bytes == old(PROJECT + "/proof-source-lock.json"))
retained = [r for r in copy_lock["copies"] if r["module"].startswith("NLA.TR06.")]
check("all-58-retained-published-sources-including-credits-unchanged", len(retained) == 58
      and all(current(r["source"]) == current(r["destination"]) == old(r["destination"], PUBLISHED)
              for r in retained))
check("intrinsic-Target-Infrastructure-and-Reviewed-still-exact-originals",
      current(PROJECT + "/NLA/Statements/TR06.lean") == old("lean-statements/NLA/Statements/TR06.lean", STATEMENT)
      and current(PROJECT + "/NLA/Statements/Infrastructure.lean") == old("lean-statements/NLA/Statements/Infrastructure.lean", STATEMENT)
      and current(PROJECT + "/Reviewed/TR06.lean") == old("lean-statements/Reviewed/TR06.lean", STATEMENT))

proof_reviews = [json.loads(current(V + "/linux-ci/2b049df5/" + name))
                 for name in ["root-review-2026-10-23.json", "independent-review-2026-10-23.json"]]
check("two-actual-proof-commit-strict45-replays-pass", all(r["passed"] and r["source_commit"] == PROOF
      and len(r["checks"]) == 45 and all(c["passed"] for c in r["checks"]) for r in proof_reviews))
check("promotion-descriptions-honestly-require-fresh-CI",
      b"separate fresh Linux receipt" in readme
      and b"descriptive-promotion-refresh-pending" in current(PROJECT + "/formalization.yaml")
      and b"separate fresh Linux receipt" in current(PROJECT + "/README.md"))

renderer = ast.parse(current("tools/render_problems.py"))
old_renderer = ast.parse(old("tools/render_problems.py"))
class RemoveNewTR06SetEntries(ast.NodeTransformer):
    def visit_Set(self, node):
        node.elts = [e for e in node.elts if not (isinstance(e, ast.Constant) and e.value == "TR-06")]
        return self.generic_visit(node)
check("renderer-only-two-TR06-specific-set-additions",
      sum(isinstance(e, ast.Constant) and e.value == "TR-06" for n in ast.walk(renderer)
          if isinstance(n, ast.Set) for e in n.elts) == 2
      and ast.dump(RemoveNewTR06SetEntries().visit(renderer)) == ast.dump(old_renderer))
tex = current("tensor-computations/TR-06/problem.tex")
tex = re.sub(rb"\\subsection\{Lean proof and verification evidence.*?(?=\\subsection\{Resolution --- 2026-09-11\})",
             b"", tex, count=1, flags=re.S)
tex = tex.replace(b"Verification check: 2026-10-23", b"Literature check: 2026-09-11", 1)
tex = tex.replace(b"Status: Lean verified", b"Status: Solved", 1)
tex = tex.replace(b"\\newpage\n\n\\subsection{Context and notation}", b"\\subsection{Context and notation}", 1)
check("rendered-TeX-original-content-preserved-modulo-whitespace-and-authorized-layout",
      re.sub(rb"\s", b"", tex) == re.sub(rb"\s", b"", old("tensor-computations/TR-06/problem.tex", ORIGINAL)))

counts = Counter(re.search(rb"^\*\*Status:\*\* (.*?)\s*$", current(p), re.M)[1].decode()
                 for p in registry.values())
check("catalog-counts-84-verified-34-Solved-217-retained-IDs", counts["Lean verified"] == 84
      and counts["Solved"] == 34 and sum(counts.values()) == 217
      and b"34 solved (published or independently audited); 84 solved with Lean verification." in current("CATALOG.md"))
inventory = json.loads(current("docs/lean/statements/inventory.json"))
prior_inventory = json.loads(old("docs/lean/statements/inventory.json"))
entries_key = next(k for k, value in inventory.items() if isinstance(value, list)
                   and value and isinstance(value[0], dict) and "id" in value[0])
now_entry = next(r for r in inventory[entries_key] if r["id"] == "TR-06")
before_entry = next(r for r in prior_inventory[entries_key] if r["id"] == "TR-06")
restored_inventory = json.loads(json.dumps(inventory))
restored_inventory[entries_key] = [before_entry if r["id"] == "TR-06" else r for r in restored_inventory[entries_key]]
check("statement-inventory-only-authorized-TR06-status-hash-change",
      restored_inventory == prior_inventory and now_entry["status"] == "Lean verified"
      and now_entry["canonical_sha256"] == digest(readme)
      and now_entry["published_sha256"] == before_entry["published_sha256"]
      and now_entry["canonical_unchanged_from_base"] is False)

report = {"reviewer": "/root/recover_verification (independent non-proof-author Codex AI agent)",
          "date": "2026-10-23", "scope": "Concrete descriptive/status promotion and exact original/proof preservation; fresh promotion Linux receipt required",
          "frozen_promotion_lock": FREEZE, "frozen_promotion_lock_sha256": digest(freeze_bytes),
          "accepted_proof_commit": PROOF, "original_archive_commit": ORIGINAL,
          "checks": checks, "passed": all(c["passed"] for c in checks),
          "promotion_Linux_accepted": False, "other_canonical_pages": other_pages,
          "original_archives": archives, "unchanged_Lean_inputs": unchanged_lean,
          "source_copies": copies, "catalog_counts": dict(counts),
          "current_locked_inputs": freeze["records"],
          "limitations": ["Status promotion review does not claim exact-input CI for the modified descriptive package.",
                          "The actual Linux acceptance remains bound to proof commit2b049df5 until a fresh promotion receipt is accepted."]}
(OUT / "result.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"passed": report["passed"], "controls": len(checks),
                  "failed_controls": [c["name"] for c in checks if not c["passed"]]}, indent=2))
raise SystemExit(0 if report["passed"] else 1)
