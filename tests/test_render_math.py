"""Check that GitHub math retains its equations and PDF-only layout in Pandoc."""

import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import render_problems


class PdfMetadataAndLayoutTests(unittest.TestCase):
    def test_protected_math_title_has_no_wrapper_backticks(self):
        plain = r"Exact bilinear rank of the $3\times3$ matrix product"
        protected = r"Exact bilinear rank of the $`3\times3`$ matrix product"
        self.assertEqual(render_problems.plain_pdf_title(protected),
                         render_problems.plain_pdf_title(plain))
        self.assertIn("3 × 3", render_problems.plain_pdf_title(protected))
        self.assertEqual(render_problems.plain_pdf_title("A `literal` title"),
                         "A `literal` title")

    def test_removed_public_layout_commands_return_at_original_headings(self):
        cases = {
            "MF-22": ("## Resolution: affirmative, 11 September 2026", r"\pagestyle{plain}"),
            "RA-12": ("## Problem statement", r"\newpage"),
            "RA-13": ("## Problem statement", r"\newpage"),
        }
        for identifier, (heading, command) in cases.items():
            with self.subTest(identifier=identifier):
                body = f"Earlier material.\n\n{heading}\n\nOriginal target.\n"
                restored = render_problems.restore_pdf_layout(identifier, body)
                self.assertEqual(restored, body.replace(heading, command + "\n\n" + heading))
                self.assertEqual(render_problems.restore_pdf_layout("MF-21", body), body)


class PandocMathTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.pandoc = shutil.which(os.environ.get("PANDOC", "pandoc"))
        if cls.pandoc is None:
            raise unittest.SkipTest("Pandoc is required; set PANDOC to its executable")

    def convert(self, markdown, *, filtered=True, output="json", extra=()):
        command = [self.pandoc, "--from=" + render_problems.MARKDOWN_READER,
                   "--to=" + output]
        if filtered:
            command.append("--lua-filter=" + str(render_problems.MATH_FILTER))
        command.extend(extra)
        result = subprocess.run(command, input=markdown, text=True,
                                capture_output=True, check=True)
        return json.loads(result.stdout) if output == "json" else result.stdout

    def assert_same_equations_and_tex(self, ordinary, github):
        def trim_math_padding(node):
            # Dollar displays retain delimiter-adjacent newlines in the AST;
            # code fences do not. Compare the equation, including internal rows.
            if isinstance(node, dict):
                if node.get("t") == "Math":
                    node["c"][1] = node["c"][1].strip()
                for value in node.values():
                    trim_math_padding(value)
            elif isinstance(node, list):
                for value in node:
                    trim_math_padding(value)
            return node

        def trim_display_padding(tex):
            return re.sub(r"\\\[\s*(.*?)\s*\\\]",
                          lambda match: r"\[" + match[1] + r"\]", tex, flags=re.S)

        self.assertEqual(trim_math_padding(self.convert(ordinary, filtered=False)),
                         trim_math_padding(self.convert(github)))
        self.assertEqual(trim_display_padding(self.convert(ordinary, filtered=False, output="latex")),
                         trim_display_padding(self.convert(github, output="latex")))

    def test_protected_inline_preserves_macros_and_norm_backslashes(self):
        formulas = [r"\|A\|_2\|A^{-1}\|_2",
                    r"\left\lVert A^*A-I\right\rVert_{\mathrm{op}}",
                    r"\mathop{\mathrm{rank}}\nolimits_{\mathbb Q}(B)\le r",
                    r"\operatorname{tr}(A)=\sum_{i=1}^n a_{ii}",
                    r"\{x\in\mathbb R^n:x_i\ge0\}"]
        for formula in formulas:
            with self.subTest(formula=formula):
                self.assert_same_equations_and_tex(f"Assume ${formula}$.",
                                                   f"Assume $`{formula}`$.")

    def test_multiline_fence_preserves_aligned_rows(self):
        formula = (r"\begin{aligned}" + "\n" +
                   r"B_0&=\begin{pmatrix}0&-5\\16&-5\end{pmatrix},\\" + "\n" +
                   r"\|A\|_2&\le\mathop{\mathrm{polylog}}\nolimits(n)." + "\n" +
                   r"\end{aligned}")
        self.assert_same_equations_and_tex(f"Before.\n\n$$\n{formula}\n$$\n\nAfter.",
                                           f"Before.\n\n```math\n{formula}\n```\n\nAfter.")

    def test_fenced_math_stays_in_ordered_and_bullet_lists(self):
        for marker, indent in [("1.", "   "), ("-", "  ")]:
            with self.subTest(marker=marker):
                formula = r"|R_{p,n,j}|\le D_p(n+2)^{-p-1}"
                prefix = f"{marker} For every index:\n\n"
                suffix = f"\n\n{indent}The same constants apply.\n"
                ordinary = prefix + f"{indent}$$\n{indent}{formula}\n{indent}$$" + suffix
                github = prefix + f"{indent}```math\n{indent}{formula}\n{indent}```" + suffix
                self.assert_same_equations_and_tex(ordinary, github)

    def test_currency_and_literal_code_are_untouched(self):
        markdown = (r"Cost is \$5 and \$10; a literal `\|A\|_2` is code." + "\n\n" +
                    '``$`x`$`` and `$x$` are code examples.\n\n' +
                    '```python\nprint("$`x`$")\n```\n\n' +
                    '````text\n```math\nx^2\n```\n````\n')
        self.assertEqual(self.convert(markdown, filtered=False), self.convert(markdown))

    def test_legacy_math_and_raw_page_directives_are_untouched(self):
        markdown = r"\newpage" + "\n\n" + r"Legacy $\alpha$ and $$\|A\|_2\le1$$." + "\n"
        self.assertEqual(self.convert(markdown, filtered=False), self.convert(markdown))

    def test_protected_math_is_parsed_in_title_metadata(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "metadata.json"
            path.write_text(json.dumps({"title": r"Rank of $3\times3$ matrices"}))
            original = self.convert("Body.", filtered=False,
                                    extra=("--metadata-file=" + str(path),))
            path.write_text(json.dumps({"title": r"Rank of $`3\times3`$ matrices"}))
            github = self.convert("Body.", extra=("--metadata-file=" + str(path),))
            self.assertEqual(original, github)


if __name__ == "__main__":
    unittest.main()
