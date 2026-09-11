# Round-three submissions - 11 September 2026

Author: **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom. Email: **m.colbrook@damtp.cam.ac.uk**. [Official affiliation](https://www.damtp.cam.ac.uk/user/mjc249/home.html), checked 11 September 2026. Authorship is recorded at the submitter's explicit request.

| Entry | Outcome | Primary proof | Independent review |
|---|---|---|---|
| IE-10 | Solved: exact complex cyclic model, C=1700 and c=3 | [Manuscript](manuscripts/IE-10.pdf) | [Full review](verification/reviews/IE-10-review.md) |
| IS-04 | Partially resolved: explicit prime-square family; all orders remain unresolved | [Manuscript](manuscripts/IS-04.pdf) | [Full review](verification/reviews/IS-04-review.md) |

Both original manuscripts and computational support were supplied as AI-generated work. Two separate independent agents audited the complete proofs against the canonical statements and checked the cited primary sources. Reviews hash the complete Markdown and TeX sources using UTF-8/LF with no trimming. Attributed exports preserve the original mathematical bodies and add author, date and subsequent review notices. Original pending-review remarks are superseded by those dated reports. This is independent agent verification, not external human peer review or formal proof-assistant certification. No novelty or historical priority claim is made.

All 28 original files are retained byte-for-byte in [submitted](submitted/START_HERE.md), including the original PDFs, source register, verification programs and nested support archive. All 27 entries of the supplied SHA256 manifest match. [Archive identity](bundle-sha256.json) records the archive hash and nested inventory. Original research/search reports describe the supplied work and are not represented as newly repeated searches.

Fresh [exact and numerical checks](verification/fresh-check-results.json) pass: symbolic identities, 200 Krylov matrices and 2530 eigenpairs, physical-model comparisons, finite differences, 11 sampled root paths and 18 prime-field constructions through p=1009. Fresh [140-digit stress checks](verification/fresh-stress-results.json) pass eight cases and 46 eigenpairs. Finite computations support the independently reviewed analytic proofs; sampled root paths and floating-point FFTs do not certify uniform theorems. The classical character-sum theorem and its specialization are identified in the IS-04 review.

Rebuild the attributed manuscripts with `python tools/render_reviewed_tex.py references/colbrook-round3-2026-09-11/manuscripts.json`. Rebuild canonical documents with `python tools/render_problems.py IE-10 IS-04`. Run the supplied scripts from `submitted/verification` with `--output` directed to a fresh output path; retain the original submitted files unchanged.

[Document checks](verification/document-checks.json): all four PDFs compile without reported warnings and all 16 pages were visually inspected. Complete proof bodies, original canonical content, local links, all 203 permanent IDs and catalog idempotence pass. Local safeguard tests pass 15 cases; two symlink cases require unavailable Windows privileges (error 1314). The unchanged full suite runs in Linux CI. The branch catalog has 178 open targets: 98 Open and 80 Partially resolved, plus 1 Solution claimed and 24 Solved.
