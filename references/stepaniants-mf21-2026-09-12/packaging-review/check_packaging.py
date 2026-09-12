#!/usr/bin/env python3
"""Read-only MF-21 publication-conversion checks.

This checker does not verify the mathematical theorem or write in the
publication worktree. Its stdout is a JSON audit record.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess
import unicodedata
from urllib.parse import unquote, urlsplit

parser = argparse.ArgumentParser()
parser.add_argument("worktree", nargs="?", default="/tmp/nla-mf21-worktree")
parser.add_argument("--complete-references", action="store_true")
parser.add_argument("--allow-pending-assembly", action="store_true",
                    help="Allow only the three explicitly named final assembly outputs.")
args = parser.parse_args()
root = Path(args.worktree).resolve()
problem = root / "matrix-functions-and-stability/MF-21"
ref = root / "references/stepaniants-mf21-2026-09-12"
urlbase = "https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/"
pandoc = os.environ.get("PANDOC") or shutil.which("pandoc")
if not pandoc:
    fallback = Path("/tmp/nla-submission-tools/pandoc-3.11-arm64/bin/pandoc")
    if fallback.is_file():
        pandoc = str(fallback)
if not pandoc:
    raise SystemExit("Set PANDOC to an installed Pandoc executable.")


def fingerprint(path):
    data = path.read_bytes()
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def norm_math(s):
    return re.sub(r"\s+", "", s)


def formulas(text, fmt):
    pattern = (r"\$\$(.*?)\$\$|(?<!\\)\$(.*?)(?<!\\)\$"
               if fmt == "markdown" else r"\\\[(.*?)\\\]|\\\((.*?)\\\)")
    return [norm_math(a if a else b) for a, b in re.findall(pattern, text, re.S)]


def ast(text, fmt):
    result = subprocess.run(
        [pandoc, "--from=" + fmt, "--to=json"],
        input=text, text=True, capture_output=True, check=True,
    )
    return json.loads(result.stdout)


def visible(node, raw):
    if isinstance(node, list):
        return "".join(visible(x, raw) for x in node)
    if not isinstance(node, dict):
        return ""
    kind, content = node.get("t"), node.get("c")
    if kind == "Str":
        return content
    if kind in ("Space", "SoftBreak", "LineBreak"):
        return " "
    if kind == "Math":
        return " [MATH] "
    if kind in ("RawInline", "RawBlock"):
        raw.append(content)
        return ""
    if kind == "Header":
        return visible(content[2], raw) + "\n"
    if kind in ("Link", "Image", "Span"):
        return visible(content[1], raw)
    if kind == "Quoted":
        return '"' + visible(content[1], raw) + '"'
    if kind in ("Code", "CodeBlock"):
        return content[1]
    if kind == "OrderedList":
        return visible(content[1], raw)
    if kind in ("Para", "Plain"):
        return visible(content, raw) + "\n"
    return visible(content, raw)


def links(node):
    out = []
    if isinstance(node, list):
        for child in node:
            out += links(child)
    elif isinstance(node, dict):
        if node.get("t") == "Link":
            out.append(node["c"][2][0])
        out += links(node.get("c", []))
    return out


def norm_prose(text):
    text = unicodedata.normalize("NFC", text)
    text = text.translate(str.maketrans({
        "\u2018": "'", "\u2019": "'", "\u201c": '"', "\u201d": '"',
        "\u2013": "-", "\u2014": "-", "\u00a0": " ",
    }))
    return " ".join(text.split())


def expand_link(link):
    if urlsplit(link).scheme or link.startswith("#"):
        return link
    path, sep, anchor = link.partition("#")
    resolved = (problem / unquote(path)).resolve().relative_to(root)
    return urlbase + resolved.as_posix() + (sep + anchor if sep else "")


def compare(md_name, tex_name, canonical=False):
    md, tex = (problem / md_name).read_text(), (problem / tex_name).read_text()
    m_math, t_math = formulas(md, "markdown"), formulas(tex, "latex")
    assert m_math == t_math, (md_name, "ordered formulas differ")
    md_body = md
    tex_body = tex.split(r"\begin{document}", 1)[1].rsplit(r"\end{document}", 1)[0]
    if canonical:
        md_body = md_body[md_body.index("**Rating rationale:**"):]
        tex_body = tex_body[tex_body.index(r"\textbf{Rating rationale:}"):]
    tex_body = re.sub(r"\\Needspace\{[^{}]*\}", "", tex_body)
    tex_body = re.sub(r"\\nopagebreak\[[0-9]+\]", "", tex_body)
    tex_body = tex_body.replace(r"\newpage", "")
    m_ast = ast(md_body, "markdown+tex_math_dollars+raw_tex")
    t_ast = ast(tex_body, "latex")
    m_raw, t_raw = [], []
    mp = norm_prose(visible(m_ast["blocks"], m_raw))
    tp = norm_prose(visible(t_ast["blocks"], t_raw))
    if mp != tp:
        import difflib
        difference = "\n".join(difflib.unified_diff(mp.split(), tp.split()))
        raise AssertionError((md_name, "visible prose differs", difference[:12000]))
    expected_links = [expand_link(x) for x in links(m_ast["blocks"])]
    actual_links = links(t_ast["blocks"])
    assert expected_links == actual_links, (md_name, "ordered links differ")
    assert not m_raw and not t_raw, (md_name, "unexamined raw content", m_raw, t_raw)
    return {
        "ordered_formulas": len(m_math),
        "formulas_identical_modulo_whitespace": True,
        "visible_prose_identical_after_typographic_normalization": True,
        "prose_characters_after_normalization": len(mp),
        "ordered_links": len(expected_links),
        "link_conversion_correct": True,
        "unexamined_raw_content": 0,
    }


record = {"checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat()}
record["solution_conversion"] = compare("solution.md", "solution.tex")
record["canonical_conversion"] = compare("README.md", "problem.tex", canonical=True)
record["artifacts"] = {
    name: fingerprint(problem / name)
    for name in ["solution.md", "solution.tex", "solution.pdf",
                 "README.md", "problem.tex", "problem.pdf"]
}

frozen = (ref / "reviewed-proof.md").read_text()
assert fingerprint(ref / "reviewed-proof.md")["sha256"] == \
    "98eb74a858ad3d2bf5fd0055a92d9c96b9a5e4f4f531972cd429462acb2b44f5"
publication = (problem / "solution.md").read_text()
repair_data = json.loads((ref / "editorial-conversion.json").read_text())
repaired = frozen
for old, new in repair_data["explicit_math_delimiter_and_prose_repairs"]:
    assert repaired.count(old) == 1
    repaired = repaired.replace(old, new)
start, end = "## 1. Exact conclusion", "## 6. Sources, attribution"
core = repaired[repaired.index(start):repaired.index(end)]
published_core = publication[publication.index(start):publication.index(end)]
assert core == published_core
record["reviewed_core"] = {
    "frozen_source": fingerprint(ref / "reviewed-proof.md"),
    "explicit_editorial_repairs": 3,
    "mathematical_sections_identical_after_repairs": True,
    "core_bytes": len(core.encode()),
    "core_sha256": hashlib.sha256(core.encode()).hexdigest(),
}
old = (ref / "canonical-statement.md").read_text()
new = (problem / "README.md").read_text()
old_suffix = old[old.index("## Statement"):]
new_suffix = new[new.index("## Statement"):new.index("## Resolution audit")].rstrip() + "\n"
assert old_suffix == new_suffix
assert old.splitlines()[0] == new.splitlines()[0]
accepted_registry = subprocess.check_output(
    ["git", "-C", str(root), "show", "HEAD:problem_ids.json"]
)
assert (root / "problem_ids.json").read_bytes() == accepted_registry
record["canonical_preservation"] = {
    "original_statement_and_history_bytes": len(old_suffix.encode()),
    "original_statement_and_history_sha256": hashlib.sha256(old_suffix.encode()).hexdigest(),
    "original_statement_and_history_identical": True,
    "title_identical": True,
    "registry_identical_to_HEAD": True,
    "registry_mappings": len(json.loads(accepted_registry)),
}

expected_byline = [
    "George Stepaniants",
    "Department of Computing and Mathematical Sciences",
    "California Institute of Technology",
    "Pasadena, California, USA",
]
for name in ["solution.md", "README.md"]:
    text = (problem / name).read_text()
    for phrase in expected_byline:
        assert phrase in text, (name, phrase)
    assert "Substantial AI assistance" in text
    assert "formal verification" in text
record["visible_metadata"] = {
    "full_name_and_affiliation": True,
    "ai_assistance_and_informal_review_limits": True,
}
pdf_metadata = {}
email_re = re.compile(r"(?<![\w.+-])[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}")
for name in ["solution.pdf", "problem.pdf"]:
    pdf = problem / name
    info = subprocess.check_output(["pdfinfo", str(pdf)], text=True)
    extracted = subprocess.check_output(["pdftotext", str(pdf), "-"], text=True)
    assert not email_re.search(info + extracted) and "mailto:" not in info + extracted
    parsed = dict(line.split(":", 1) for line in info.splitlines() if ":" in line)
    pdf_metadata[name] = {
        key: parsed.get(key, "").strip() for key in ["Title", "Author", "Pages"]
    }
    pdf_metadata[name]["no_contact_email_in_metadata_or_extracted_text"] = True
assert pdf_metadata["solution.pdf"]["Author"] == "George Stepaniants"
assert pdf_metadata["solution.pdf"]["Pages"] == "7"
record["pdf_metadata_and_privacy"] = pdf_metadata
resolved = (root / "RESOLVED.md").read_text()
section = re.search(r"(?ms)^### .*MF-21.*?(?=^### |\Z)", resolved).group(0)
for phrase in expected_byline:
    assert phrase in section
assert not email_re.search(section) and "mailto:" not in section
record["resolved_notice"] = {
    "full_name_and_affiliation": True,
    "no_contact_email": True,
}

if args.complete_references:
    binding_counts = {}
    manifests = [
        ("independent-review-manifest.json", "files"),
        ("supporting-manifest.json", "files"),
        ("source-scope-manifest.json", None),
    ]
    for manifest_name, field in manifests:
        data = json.loads((ref / manifest_name).read_text())
        entries = data[field] if field else data
        if isinstance(entries, list):
            items = [(entry["path"], entry) for entry in entries]
        else:
            items = list(entries.items())
        for name, expected in items:
            archived_name = name
            if manifest_name == "supporting-manifest.json":
                archived_name = {"RESULT.md": "reviewed-proof.md",
                                 "exact-check.json": "original-exact-check.json"}.get(name, name)
            actual = fingerprint(ref / archived_name)
            if manifest_name == "supporting-manifest.json" and name == "exact_check.py":
                adapted = (ref / name).read_bytes()
                restored = adapted.replace(b"reviewed-proof.md", b"RESULT.md")
                actual = {"bytes": len(restored),
                          "sha256": hashlib.sha256(restored).hexdigest()}
            assert actual == {k: expected[k] for k in ("bytes", "sha256")}, \
                (manifest_name, name, actual, expected)
        binding_counts[manifest_name] = len(items)
    frozen_manifest = json.loads((ref / "frozen-manifest.json").read_text())
    assert frozen_manifest["source"] == "RESULT.md"
    assert fingerprint(ref / "reviewed-proof.md") == {
        k: frozen_manifest[k] for k in ("bytes", "sha256")
    }
    assert fingerprint(ref / frozen_manifest["canonical_source"])["sha256"] == \
        frozen_manifest["canonical_sha256"]
    assert fingerprint(ref / "independent-review.md") == \
        fingerprint(ref / "independent-math-review.md")
    assert fingerprint(ref / "independent-review.md")["sha256"] == \
        "3c7611724de24ce996ea313041a3d2962134e356ffa776ceef8a3df5560f6c3a"
    record["archive_bindings"] = {
        "manifest_file_entries_checked": binding_counts,
        "frozen_source_and_canonical_binding": True,
        "linked_review_is_exact_frozen_mathematical_report": True,
        "mathematical_report": fingerprint(ref / "independent-review.md"),
        "historical_names_mapped_as_documented": {
            "RESULT.md": "reviewed-proof.md",
            "original author exact-check.json": "original-exact-check.json",
        },
        "author_checker_only_changes_input_filename": True,
    }
    reference_files = [x for x in ref.rglob("*") if x.is_file()]
    banned = [str(x.relative_to(root)) for x in reference_files
              if x.suffix.lower() in (".pdf", ".png", ".jpg", ".jpeg", ".webp")]
    assert not banned, ("unexpected third-party/binary reference assets", banned)
    scanned, missing, emails, pending = [], [], [], []
    allowed_pending = {"manifest.json", "verification.json",
                       "packaging-review/MF-21-packaging-review.md"}
    files = [problem / "README.md", problem / "solution.md",
             problem / "solution.tex", problem / "problem.tex"] + reference_files
    for path in files:
        text = path.read_text()
        is_code = path.suffix.lower() in {".py", ".js", ".mjs", ".cjs", ".ts", ".sh"}
        if email_re.search(text) or (not is_code and "mailto:" in text):
            emails.append(str(path.relative_to(root)))
        if path.suffix.lower() != ".md":
            continue
        tree = ast(text, "markdown+tex_math_dollars+raw_tex")
        for target in links(tree["blocks"]):
            parsed = urlsplit(target)
            if parsed.scheme or target.startswith("#"):
                continue
            context = path.parent
            if path.name in ("canonical-statement.md", "canonical-target.md"):
                context = problem
            resolved = (context / unquote(parsed.path)).resolve()
            scanned.append({"source": str(path.relative_to(root)), "target": target})
            if not resolved.exists():
                if args.allow_pending_assembly and resolved.is_relative_to(ref) \
                        and resolved.relative_to(ref).as_posix() in allowed_pending:
                    pending.append(scanned[-1])
                else:
                    missing.append(scanned[-1])
    assert not emails, ("email address or mailto found", emails)
    assert not missing, ("missing relative Markdown links", missing)
    record["reference_links_and_privacy"] = {
        "reference_files": len(reference_files),
        "relative_links_checked": len(scanned),
        "missing": missing,
        "pending_assembly_links": pending,
        "snapshot_navigation_interpreted_at_original_canonical_location": True,
        "email_or_mailto_files": emails,
        "reference_pdf_or_image_assets": banned,
    }
record["verdict"] = "PASS: conversion and packaging checks only; not a proof verifier"
print(json.dumps(record, indent=2))
