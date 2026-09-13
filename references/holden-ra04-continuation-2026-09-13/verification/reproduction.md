# Submission validation — 2026-09-13

The coordinating agent reran both submitted checkers. Exact arithmetic passed 459 coloring cases, three rational graph fixtures and the boundary-rank example; the separate reviewer independently reproduced the exact checks. The NumPy run generated 27 diagnostics, which are not universal probability tests.

The permanent-ID validator passed against origin/main and upstream/main (217 IDs). All 17 permanent-ID regression tests passed. Catalog regeneration preserves 125 open targets: 52 Open and 73 Partially resolved, compared with 53 and 72 on this PR's upstream base. The original mathematical statement is unchanged. The math-format check passed, and the affected canonical TeX/PDF was regenerated with the repository renderer. Both final PDFs were visually inspected; the report compiles without warnings or overfull boxes. The canonical notice was shortened during layout review without changing the audited scope. No Lean checks were run.

Commands:

```sh
python3 tests/exact_checks.py --output verification/exact_checks.json
python3 tests/numerical_checks.py --output verification/numerical_checks.json
bash build.sh
# From the repository root:
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
python3 -m unittest discover -s tests -p 'test_problem_statuses.py' -v
python3 tools/format_math.py --check
python3 tools/render_problems.py RA-04
```

The renderer used the available Pandoc binary via its documented PANDOC override, and system XeLaTeX; the report used system pdfLaTeX. Numerical diagnostics used the bundled Python/NumPy runtime. Exact checks and catalog tools used system Python.
