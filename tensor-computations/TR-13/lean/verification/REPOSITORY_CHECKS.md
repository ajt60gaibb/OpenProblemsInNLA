# Repository checks — 28 September 2026

These are the coordinating agent's recorded check results, not a transcript of
the authoritative Linux verifier. The Lean compiler and axiom transcript is
retained separately in `macos-full.log`.

| Check | Result |
| --- | --- |
| `tools/lean/validate_manifest.py tensor-computations/TR-13/lean` | PASS, one complete target declaration |
| `tools/lean/projects.py --base-ref origin/main` | Selects only TR-13 |
| `tools/validate_problem_ids.py --base-ref origin/main` | PASS, 217 permanent IDs |
| `tools/update_catalog.py --base-ref origin/main` | PASS; no counts or generated index bytes changed |
| `python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v` | PASS, 17 tests |
| `python3 -m unittest discover -s tests -p 'test_lean_verification.py' -v` | PASS, 30 tests |
| `tools/format_math.py --check TR-13` | PASS, zero pages needing normalization |
| `tools/render_problems.py TR-13` | PASS; two-page PDF visually inspected |
| `git diff --check` | PASS |
| Source hash equality against the compiled temporary project | PASS for every recorded file |
| Project/review/verification index links | PASS |

Python metadata validators were installed at the versions in
`tools/lean/requirements.txt` in a temporary virtual environment. The PDF layout
places the retained original statement on its own page; the mathematical target
is unchanged.
