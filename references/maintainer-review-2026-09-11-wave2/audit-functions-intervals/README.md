# PR47 / PR62 independent review record

Both frozen heads passed independent mathematical review in the stated scope. No blocking proof or canonical-target error was found.

- [PR47 detailed review](PR47-REVIEW.md): 6 entries; MF-14 and MF-15 remain partial, MF-18 remains an auxiliary contribution to an unresolved canonical target.
- [PR62 detailed review](PR62-REVIEW.md): 7 entries; three hardness results are complexity classifications, not proofs that P differs from NP.
- `independent_checks.py` and `independent-check-results.json`: fresh exact checks, with no imports of submitted verifiers.
- `pr47-submitted-certificates.log`: 7 audited exact certificate programs, all PASS.
- `pr62-run/verification/`: full exact suite results and AV-01 exact feasibility comparison results.
- `pdf-qa/`: 73-page read-only visual QA, original hashes and extracted text for 25 final PDFs.
- `pdf-source-rebuild-results.json`: every PDF's text reproduced from unchanged TeX sources. No build warnings. Two benign spacing-only raster differences separately inspected.

The mathematical reviews are independent agent analyses with exact computations, not proof-assistant formalization, external human peer review, or exhaustive novelty verification. The frozen submissions and shared integration checkout were not modified.

## Reproduce in this environment

Fresh exact identities:

```bash
PYTHONPATH=/private/tmp/nla-pr-review-20260911/python-deps /Users/ajt253/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3 -B independent_checks.py
```

Audited interval suite (working copies write outputs only under this audit folder):

```bash
PYTHONPATH=/private/tmp/nla-pr-review-20260911/python-deps /Users/ajt253/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3 -B pr62-run/code/verify_exact.py --full
PYTHONPATH=/private/tmp/nla-pr-review-20260911/python-deps /Users/ajt253/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3 -B pr62-run/code/verify_av01_exact.py --full
```

Audited matrix-function certificates:

```bash
python3 -B ../pr-47/references/colbrook-matrix-functions-2026-09-11/code/run_certificates.py
```

PDF QA/reproduction uses `pymupdf`, Pillow and XeLaTeX. The available `pymupdf` path is `/private/tmp/higham-elimination/python-packages`, usable as PYTHONPATH with the bundled Python.


Archival note: local snapshot and runtime paths identify the audit environment. This published record includes review prose, independent check sources and JSON results; transient PDF page images, build trees and copied contributor inputs remain in the local audit archive. The original submissions are identified by the frozen Git commits above.
