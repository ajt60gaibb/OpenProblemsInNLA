#!/usr/bin/env python3
"""Verify the final IE-05 GitHub/PDF layout separation without rebuilding PDFs.

The prior README and renderer are reconstructed exactly from the current files.
The actual render() functions run only as far as their Pandoc invocation, which
is intercepted. No compiler runs and no canonical TeX or PDF is written.
"""
from pathlib import Path
import hashlib
import json
from unittest.mock import patch


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PROBLEM = ROOT / "linear-systems-and-elimination/IE-05"
RENDERER = ROOT / "tools/render_problems.py"
BLOCK = '''    if identifier == "IE-05":
        # Keep the unchanged original target together after its resolution notice.
        # This PDF-only layout instruction should not appear on the GitHub page.
        body = body.replace("## Context and notation\\n", "\\\\newpage\\n\\n## Context and notation\\n", 1)
'''


def fingerprint(data):
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


class Captured(Exception):
    pass


class Source:
    parent = PROBLEM

    def __init__(self, markdown):
        self.markdown = markdown

    def read_text(self):
        return self.markdown


def pandoc_input(code, markdown):
    namespace = {"__name__": "ie05_layout_audit", "__file__": str(RENDERER)}
    exec(compile(code, str(RENDERER), "exec"), namespace)
    captured = {}

    def intercept(command, **kwargs):
        assert "--from=markdown+tex_math_dollars+raw_tex" in command
        captured["body"] = kwargs["input"].encode()
        metadata = next(x.split("=", 1)[1] for x in command if x.startswith("--metadata-file="))
        captured["metadata"] = Path(metadata).read_bytes()
        raise Captured

    with patch("subprocess.run", side_effect=intercept):
        try:
            namespace["render"](Source(markdown))
        except Captured:
            pass
    assert set(captured) == {"body", "metadata"}
    return captured


def main():
    old_manifest = json.loads((HERE / "document-checks-before-layout-move.json").read_text())
    current = (PROBLEM / "README.md").read_text()
    marker = "## Context and notation\n"
    assert current.count(marker) == 1 and "\\newpage" not in current
    old = current.replace(marker, "\\newpage\n\n" + marker, 1)
    readme_path = str((PROBLEM / "README.md").relative_to(ROOT))
    assert fingerprint(old.encode()) == old_manifest["files"][readme_path]
    new_renderer = RENDERER.read_text()
    assert new_renderer.count(BLOCK) == 1
    old_renderer = new_renderer.replace(BLOCK, "", 1)
    assert fingerprint(old_renderer.encode())["sha256"] == "92ec0bcfd8a9c224e26183e790bb8a7ac23b707019354b0ef3844a9b3fb5f91f"
    previous_input = pandoc_input(old_renderer, old)
    current_input = pandoc_input(new_renderer, current)
    assert previous_input == current_input

    unchanged = {}
    for name in ["solution.md", "solution.tex", "solution.pdf", "problem.tex", "problem.pdf"]:
        path = PROBLEM / name
        key = str(path.relative_to(ROOT))
        unchanged[key] = fingerprint(path.read_bytes())
        assert unchanged[key] == old_manifest["files"][key]

    print(json.dumps({
        "verdict": "PASS",
        "old_readme": fingerprint(old.encode()),
        "new_readme": fingerprint(current.encode()),
        "old_renderer": fingerprint(old_renderer.encode()),
        "new_renderer": fingerprint(new_renderer.encode()),
        "identical_effective_pandoc_body": fingerprint(current_input["body"]),
        "identical_pandoc_metadata": fingerprint(current_input["metadata"]),
        "unchanged_artifacts": unchanged,
        "PDF_rebuild_required": False,
        "scope": "Only the README layout command moved into its IE-05 renderer branch; no proof, target, TeX or PDF changed."
    }, indent=2) + "\n", end="")


if __name__ == "__main__":
    main()
