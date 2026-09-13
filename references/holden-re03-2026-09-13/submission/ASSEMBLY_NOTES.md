# Assembly notes

## Preserved source material

The available continuation attachment set consisted of ten files: the PDF,
three LaTeX files, three Python implementation files, one JSON report, the proof
review guide, and the previous README. All ten are preserved byte for byte.
The previous README is stored as `provenance/README.previous.md`; the other
nine retain their relative paths. The original earlier ZIP and PDF are also
included unchanged under `prior/`.

No manuscript text, proof, algorithm, or original recorded numerical result was
changed during packaging. The source input directives resolve to the supplied
LaTeX files, and the three supplied implementation modules have all their local
imports available. The PDF was not recompiled.

## Files not available from the earlier continuation

The earlier README or manuscript refers to the following absent files:

- `code/depth_family.py`
- `code/joint_regression.py`
- `code/verify.py`
- `code/verify_two_stage.py`
- `results/verification.json` and other continuation reports besides
  `results/two_stage.json`
- the earlier versions of `SOURCES.md`, `STATUS.json`, `requirements.txt`,
  `run_checks.sh`, `build_pdf.sh`, and `verify_integrity.py`

No attempt was made to recreate missing research or original verification
scripts. The manuscript bibliography remains the source index; no new
`SOURCES.md` is claimed. The prior ZIP has its own separate `SOURCES.md`,
verification code, and recorded results, which must not be substituted for
missing continuation files.

The manuscript and prior README still contain descriptions of these unavailable
materials because those documents are intentionally preserved. The full set of
reported continuation tests cannot be reproduced from the files available here.

## Packaging additions

The root README, this note, `STATUS.json`, `requirements.txt`, `build_pdf.sh`,
`run_checks.sh`, `verify_integrity.py`, `checks/assembly_smoke.py`,
`results/assembly_smoke.json`, and `SHA256SUMS.txt` were added during this assembly.
The requirements pin reflects the Python package version recorded in the
supplied JSON report and present in the assembly-check environment.

The new smoke checks are intentionally narrow. They check that the available
implementation executes through an opaque oracle, counts queries, returns
proper HODLR outputs, and handles representative fallback and sketch paths.
They do not reproduce missing Monte Carlo suites, review the proposed proofs,
or establish a worst-case error guarantee. The PDF build helper is supplied as
a convenience; a rebuild was not performed during assembly.

## Integrity scope

`SHA256SUMS.txt` covers every packaged file except itself. ZIP CRC checks and
SHA-256 verification establish byte integrity, not correctness of mathematical
content. The prior ZIP is a nested, unchanged provenance artifact.
