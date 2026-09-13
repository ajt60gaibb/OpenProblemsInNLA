# Submission validation — 13 September 2026

- Independent AI-agent audit: PASS for the partial theorem; full RA-14 remains unresolved.
- Original manifest: all 32 listed digests pass; all 33 extracted files are preserved byte-for-byte.
- Public source from the first mathematical section through the end: byte-identical to the reviewed submitted source. Editorial differences are confined to the front matter and contents formatting.
- Original canonical problem statement: byte-identical to upstream main.
- Component rerun: 28 new, 20 unchanged v4 and 17 unchanged v3 tests pass; regenerated diagnostics are in `verification/`.
- `python3 tools/validate_problem_ids.py --base-ref origin/main`: 217 IDs validated.
- `python3 tools/update_catalog.py --base-ref origin/main`: passes, with no generated index or count changes.
- `python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v`: all 17 pass.
- `python3 tools/format_math.py --check`: zero pages need formatting.
- `python3 tools/render_problems.py RA-14`: passes with Pandoc and XeLaTeX.
- Authored report: PDFLaTeX twice, no final overfull boxes or unresolved references. Page images inspected; compact contents formatting prevents an almost-empty contents overflow page. Canonical PDF: both pages inspected.
- No Lean verification was performed.
