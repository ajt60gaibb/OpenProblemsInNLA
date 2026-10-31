# Repository integration checks — 31 October 2026

Prepared against upstream `main` at
`099805ef1ce7347d373e47cccc3b2d7cf580a99e`.

The following checks passed:

- `python3 tools/validate_problem_ids.py --base-ref origin/main`:
  all 217 permanent IDs validated.
- `python3 tools/update_catalog.py --base-ref origin/main`:
  97 open targets (36 Open and 61 Partially resolved), 120 retained entries
  outside the open count. IE-03 is one of two Solution claimed entries.
- `python3 tools/format_math.py --check`: no pages need formatting.
- `python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v`:
  17 tests passed.
- `python3 -m unittest discover -s tests -p 'test_problem_statuses.py' -v`:
  3 tests passed.
- `python3 -m unittest discover -s tests -p 'test_format_math.py' -v`:
  16 tests passed.
- `python3 -m unittest discover -s tests -p 'test_render_math.py' -v`:
  11 tests passed, including a rerun after the IE-03 layout adjustment.
- `python3 tools/render_problems.py IE-03`: TeX and PDF rebuilt with Pandoc
  and XeLaTeX. Both pages of the final PDF were visually inspected.
- `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex`:
  the manuscript rebuilt from the submitted source, with output directed to
  a temporary directory. Its extracted text matches the supplied PDF.
- The original context/notation and mathematical problem statement remain
  verbatim. All eight submitted research files match the author's originals
  and the hash manifest; all local links in the submission notes, canonical
  entry, and resolution archive resolve.
- Whitespace checks passed for the integration edits. The unchanged author
  manuscript `main.tex` retains one pre-existing trailing space on its
  acknowledgements line, which a full staged `git diff --check` reports;
  the source is preserved byte for byte rather than silently normalized.

The manuscript PDF is the author's original file, not the locally rebuilt
copy. The renderer change only adjusts IE-03's page breaks, keeping its
original target intact on the second page. No Lean proof was added or run.

Before submission, upstream `main` was fetched and still matched the base
above. The author's newly published discovery account was inspected at
`matias-ma/hadamard_cp` revision
`53c1796f1f315f035f4d6b5985f69850b7ddcd0f`; the public `order4096/main.pdf`,
`matrix.npy`, `verify_construction.py`, and `verify_dense.py` have the same Git
blob hashes as the files in this submission. The account includes selected
prompts and a link to a shared conversation about an earlier, larger-order
counterexample. The conversation itself could not be retrieved by the web
reader, so no review of its contents is claimed. These provenance links do
not replace the finite verification evidence recorded here.
