import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from format_math import format_markdown, math_spans


class GitHubMathFormattingTests(unittest.TestCase):
    def test_norms_sets_and_geometric_mean_are_protected(self):
        source = r"Norm $\|V\|<d/2$, set $\{x:x>0\}$, mean $A\#B$." + "\n"
        result = format_markdown(source)
        self.assertIn(r"$`\|V\|< d/2`$", result)
        self.assertIn(r"$`\{x:x>0\}`$", result)
        self.assertIn(r"$`A\#B`$", result)
        self.assertEqual([m.body.replace(" ", "") for m in math_spans(source)],
                         [m.body.replace(" ", "") for m in math_spans(result)])

    def test_operator_spacing_and_subscript_placement(self):
        result = format_markdown(r"$\operatorname{per}A+\operatorname{rank}_{+}(B)$")
        self.assertIn(r"\mathop{\mathrm{per}}\nolimits A", result)
        self.assertIn(r"\mathop{\mathrm{rank}}\nolimits_{+}", result)
        self.assertNotIn(r"\nolimitsA", result)

    def test_display_is_a_separate_fence_with_no_stray_dollars(self):
        result = format_markdown("Set\n$$\na>b\n>c\n$$\nwhere this holds.\n")
        self.assertEqual(result, "Set\n\n```math\na>b\n>c\n```\n\nwhere this holds.\n")
        self.assertEqual(format_markdown(result), result)

    def test_list_indentation_and_equation_body_survive(self):
        source = "1. First.\n   $$\n   a=b\n   $$\n   Continuation.\n\n2. Second.\n"
        result = format_markdown(source)
        self.assertIn("\n\n   $`\\displaystyle a=b`$\n\n   Continuation.", result)
        self.assertEqual(format_markdown(result), result)

    def test_indented_math_fence_becomes_standalone_displaystyle(self):
        source = "1. Matrix:\n\n   ```math\n   \\begin{pmatrix}a&b\\\\\n   c&d\\end{pmatrix}\n   ```\n\n   Continuation.\n"
        result = format_markdown(source)
        self.assertIn(r"   $`\displaystyle \begin{pmatrix}a&b\\ c&d\end{pmatrix}`$", result)
        self.assertEqual(format_markdown(result), result)

    def test_code_and_currency_are_not_rewritten(self):
        source = 'Cost $200 per month. `$x$` and ``$`y`$``.\n\n```python\ns = "$a$"\n```\n'
        self.assertEqual(format_markdown(source), source)

    def test_number_led_math_is_not_mistaken_for_currency(self):
        source = r"Size $2 \times n$, assumption $1 \le n$, cost $200 per month, and $A$."
        expected = r"Size $`2 \times n`$, assumption $`1 \le n`$, cost $200 per month, and $`A`$."
        self.assertEqual(format_markdown(source), expected)
        self.assertEqual(format_markdown(expected), expected)

    def test_unmatched_backtick_does_not_hide_later_math(self):
        with self.assertRaisesRegex(ValueError, "Escape an unmatched literal backtick"):
            format_markdown("Use a ` character and $x$.")
        self.assertEqual(format_markdown(r"Use a \` character and $x$."),
                         r"Use a \` character and $`x`$.")

    def test_code_span_requires_an_exact_length_closing_run(self):
        source = "``do not close with ``` and $x$ here`` then $y$."
        self.assertEqual(format_markdown(source),
                         "``do not close with ``` and $x$ here`` then $`y`$.")

    def test_angle_sanitizer_collisions_are_spaced_only_in_math(self):
        source = '<span>Prose</span> and `$a<x$`.\n\n' + r'$$a<x<b,\quad c</d,\quad e<!f,\quad g<?h$$' + '\n'
        result = format_markdown(source)
        expected = '<span>Prose</span> and `$a<x$`.\n\n```math\n' + r'a< x< b,\quad c< /d,\quad e< !f,\quad g< ?h' + '\n```\n\n'
        self.assertEqual(result, expected)
        self.assertEqual(format_markdown(result), result)

    def test_multiline_inline_and_escaped_dollar(self):
        source = "$\\lim_{k\\to\\infty}\nR_k$ and $\\text{Price \\$10}$"
        result = format_markdown(source)
        self.assertIn(r"$`\lim_{k\to\infty} R_k`$", result)
        self.assertIn(r"$`\text{Price \$10}`$", result)

    def test_matrix_rows_are_not_markdown_escapes(self):
        source = r"$\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)$"
        self.assertEqual(next(math_spans(format_markdown(source))).body,
                         next(math_spans(source)).body)

    def test_pdf_directives_are_removed_only_for_known_pages(self):
        source = "Intro\n\n\\newpage\n\n## Problem statement\n"
        self.assertNotIn(r"\newpage", format_markdown(source, "RA-12"))
        self.assertEqual(format_markdown(source, "SP-01"), source)

    def test_pdf_directives_in_code_examples_are_preserved(self):
        source = "```tex\n\\newpage\n```\n\n\\newpage\n\n## Problem statement\n"
        expected = "```tex\n\\newpage\n```\n\n\n## Problem statement\n"
        self.assertEqual(format_markdown(source, "RA-12"), expected)
        inline_code = "`Example:\n\\newpage\n`\n"
        self.assertEqual(format_markdown(inline_code, "RA-12"), inline_code)

    def test_unclosed_display_and_unknown_operators_fail(self):
        with self.assertRaises(ValueError):
            format_markdown("$$\na=b")
        with self.assertRaises(ValueError):
            format_markdown(r"$\operatorname*{arg max}_x f(x)$")


if __name__ == "__main__":
    unittest.main()
