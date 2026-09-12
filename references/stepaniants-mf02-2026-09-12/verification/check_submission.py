"""Check MF-02 source preservation, exact evidence, metadata and local links.

This standard-library consistency check is not formal proof verification.
Install pdftotext or set PDFTOTEXT to its executable path.
"""
from pathlib import Path
from urllib.parse import unquote
import hashlib
import json
import os
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[3]
VER = Path(__file__).resolve().parent
REF = VER.parent
CAN = ROOT / "matrix-functions-and-stability/MF-02"
BASE = "1f22006bdaa4659fcaa0bb775a887685cd3cc566"
sha = lambda b: hashlib.sha256(b).hexdigest()


def check_manifest(directory, filename):
    manifest = json.loads((directory / filename).read_text())
    for name, record in manifest["files"].items():
        data = (directory / name).read_bytes()
        assert len(data) == record["bytes"] and sha(data) == record["sha256"], name
    return manifest


check_manifest(VER / "independent-review", "manifest.json")
check_manifest(VER / "source-review", "source-review-manifest.json")
original = (VER / "reviewed-proof.md").read_bytes()
assert len(original) == 11177 and sha(original) == "63d6a0dccebaf43b7da3dc6b2615755c3c3d24791a12527007f1276256e89ba9"
assert original == (VER / "RESULT.md").read_bytes()
assert original == (VER / "independent-review/reviewed-candidate.md").read_bytes()
assert (VER / "network-check.json").read_bytes() == (VER / "source-review/network-check-sanitized.json").read_bytes()
source = (CAN / "solution.md").read_text()
tex = (CAN / "solution.tex").read_text()


def core(s):
    s = re.sub(r"\\Needspace\{[0-9]+\\baselineskip\}\n\n", "", s)
    return s[s.index("## 1. Exact target and result"):s.index("## 6. ")]


before = core(original.decode())
after = core(source)
normalized = after
editorial = json.loads((VER / "editorial-conversion.json").read_text())
for item in editorial["allowed_editorial_replacements"]:
    assert normalized.count(item["new"]) == 1
    normalized = normalized.replace(item["new"], item["old"])
assert normalized == before, "Mathematical core changed beyond recorded scope paragraph/layout"
assert len(before.encode()) == 8725 and sha(before.encode()) == editorial["original_core_sha256"]
tex_core = tex.split(r"\subsection{1. Exact target and result}", 1)[1].split(r"\subsection{6. Attribution, scope, and verification}", 1)[0]
math = lambda s: [re.sub(r"\s+", "", a or b) for a, b in re.findall(r"\\\[(.*?)\\\]|\\\((.*?)\\\)", s, re.S)]
assert math(before) == math(after) == math(tex_core)
assert len(math(after)) == 166
frozen = json.loads((VER / "frozen-artifacts.json").read_text())
for name, record in frozen["artifacts"].items():
    data = (ROOT / name).read_bytes()
    assert len(data) == record["bytes"] and sha(data) == record["sha256"], name


def old(path):
    return subprocess.check_output(["git", "show", BASE + ":" + path], cwd=ROOT)


old_target = old("matrix-functions-and-stability/MF-02/README.md")
assert old_target == (VER / "canonical-target.md").read_bytes()
assert old_target == (VER / "source-review/canonical-statement.md").read_bytes()
assert old_target == (VER / "independent-review/canonical-target.md").read_bytes()
current_target = (CAN / "README.md").read_text()
assert old_target.decode().split("## Context and notation\n", 1)[1] == current_target.split("## Context and notation\n", 1)[1]
old_registry = json.loads(old("problem_ids.json"))
new_registry = json.loads((ROOT / "problem_ids.json").read_text())
assert len(old_registry) == 217
assert all(new_registry.get(k) == v for k, v in old_registry.items())
assert "**Status:** Solved" in current_target
for phrase in ["uniform constant-factor", "exact smallest stage count", "optimal leading constant", "same multiplication budget", "remain unanswered"]:
    assert phrase in current_target, phrase
assert not re.search(r"\bpending\b", source.lower())
assert "G. Lorentzon" in source and "H. Lorentzon" not in source
assert "already gives the uniform constant-factor order" in source

name = "George Stepaniants"
affiliation = "Department of Computing and Mathematical Sciences, California Institute of Technology"
for p in [CAN / "README.md", CAN / "solution.md", REF / "README.md", ROOT / "RESOLVED.md"]:
    assert name in p.read_text() and affiliation in p.read_text(), p
email = re.compile(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}")
for p in list(REF.rglob("*.md")) + list(REF.rglob("*.json")) + list(REF.rglob("*.tex")) + [CAN / n for n in ["README.md", "solution.md", "solution.tex", "problem.tex"]]:
    assert not email.search(p.read_text()), p
assert not list(REF.rglob("*.pdf")) and not list(REF.rglob("*.png")), "Third-party assets must remain private"
extractor = os.environ.get("PDFTOTEXT") or shutil.which("pdftotext")
if not extractor:
    raise SystemExit("Install pdftotext or set PDFTOTEXT to its executable path.")
for p in [CAN / "solution.pdf", CAN / "problem.pdf"]:
    text = subprocess.check_output([extractor, str(p), "-"], text=True)
    assert name in text and not email.search(text) and "\ufffd" not in text, p

paths = [ROOT / n for n in ["README.md", "CATALOG.md", "RESOLVED.md", "matrix-functions-and-stability/README.md"]]
paths += [CAN / "README.md", CAN / "solution.md", REF / "README.md", VER / "independent-review/MF-02-independent-review.md", VER / "source-review/REVIEW.md"]
links = 0
for p in paths:
    for url in re.findall(r"\]\(([^)]+)\)", p.read_text()):
        if re.match(r"[a-z]+:", url) or url.startswith("#"):
            continue
        assert (p.parent / unquote(url.split("#", 1)[0])).resolve().exists(), (p, url)
        links += 1
print(json.dumps({
    "result": "PASS",
    "frozen_proof_sha256": sha(original),
    "original_core_bytes": len(before.encode()),
    "original_core_sha256": sha(before.encode()),
    "published_core_bytes": len(after.encode()),
    "published_core_sha256": sha(after.encode()),
    "core_unchanged_except_one_recorded_scope_paragraph_and_layout": True,
    "ordered_original_markdown_tex_math_expressions_identical": len(math(after)),
    "independent_math_and_source_review_files_match_manifests": True,
    "all_six_canonical_artifacts_match_frozen_hashes": True,
    "entire_original_context_target_references_scope_history_unchanged": True,
    "all_217_original_permanent_ids_unchanged": True,
    "scope_and_prior_credit_explicit": True,
    "author_and_affiliation_present": True,
    "no_contact_email_in_submission_text_or_pdfs": True,
    "third_party_pdf_and_image_assets_not_redistributed": True,
    "valid_local_links": links,
}, indent=2))
