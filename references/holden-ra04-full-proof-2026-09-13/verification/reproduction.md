# Publication verification — 13 September 2026 (UTC)

- Separate independent informal mathematical audit: PASS for the complete exact target.
- Source Sections 1–7 are byte-identical to the independently reviewed original; changes are author/affiliation, PDF metadata, layout spacing, and review-status prose. Canonical original statement and all following references/history are byte-identical to upstream main.
- Fresh exact checks: PASS (5 rank witnesses, 3 interpolation fixtures, symbolic translation through 13 degrees, tied-value descent, 6 resolvent identities, 105 pole residues, 4 cover fixtures).
- Fresh numerical diagnostics: PASS; 96 head records, 81 algorithm records, 6 high-precision stress records. Only 43 algorithm records meet epsilon 0.1 at the tested depths; these finite depths are diagnostics, not the theorem's sufficient iteration count. This is not a universal numerical certification.
- Runtime: Python 3.9.6, SymPy 1.14.0, NumPy 2.0.2, mpmath 1.3.0. The supplied README recommends Python 3.11+, but these scripts successfully ran on the listed installed interpreter. Original results remain separately in results/.
- Commands: `python tests/exact_checks.py --output verification/exact_checks.json`; `python tests/numerical_checks.py --output-dir verification`; `bash build.sh`.
- 217 permanent IDs validated against origin/main and upstream/main; all 17 test_problem_ids.py tests passed; math-format check passed.
- Catalog regenerated: 124 open targets, 77 solved and 16 Lean verified retained entries. RA-04 is the sole status change.
- Manuscript and canonical TeX/PDF rebuilt. All manuscript pages visually inspected; updated first/review pages and both final canonical pages inspected. No overfull boxes or unresolved references in manuscript build.
- No Lean verification performed.
