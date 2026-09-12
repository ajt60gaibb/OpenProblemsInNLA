# PR #122 IE-02 PDF/source packaging QA

Date: 2026-09-11. Reviewer: Codex agent `/root/audit_inequalities`.

**PASS for PDF/source packaging. No packaging blocker found.** Mathematical correctness and final integration are independently reviewed by the parent and other agents.

Frozen reviewed PR head: `53dd2d078222d2346ffa20a05e602f9ae1766eef`.
Current published target-comparison base: `b8e255ccc2d51671714241ff6c3eba29d1d70f41`.

## Inspection and consistency

All seven PDF pages were rendered with Poppler to separate temporary PNGs at maximum dimension 1700 pixels and inspected individually. The canonical document has two pages; the complete solution has five. No clipping, overlap, missing glyph, broken equation or unreadable attribution was found. The full original target and its quantifiers are visible on canonical page 1, with historical references and status checks retained on page 2. The solution's first four pages contain the theorem, maximal singular-subspace description, scalar spectral factorization, simultaneous preservation, finite-dimensional optimality condition and completion; page 5 retains scope and references. Page numbers and transitions are legible.

The 157 solution and 15 canonical mathematical expressions agree in Markdown/TeX, in order and exactly after whitespace removal. The source comparison covers every inline and display expression, not only numbered equations. The complete original Problem statement section is byte-identical to published main `b8e255ccc2d51671714241ff6c3eba29d1d70f41`. The canonical ID/path and full complex Jordan-block target are preserved.

The submitted `references/stepaniants-ie02-2026-09-11/verification/check_submission.py` was read before execution. It performs local reads and invokes only read-only `git show` and `pdftotext`. Running it with `python3 -B` at the reviewed head returned PASS: the archived proof and independent-review hashes match, the 9,153-byte mathematical core matches after removing specified layout directives, all 157 proof expressions agree, the original target and 203 original ID mappings are preserved, author/affiliation checks pass and 976 local links resolve. Independently, all 22 byte lengths and hashes listed in `document-checks.json` match the frozen checkout.

George Stepaniants and his Caltech affiliation appear in the canonical document, proof and linked provenance. Prior work by Tichy, Liesen and Faber remains credited. The external Caratheodory-Fejer theorem is attributed to Courtney and Sarason with its precise locator. Substantial AI assistance and the limits of agent review are explicit. No mathematical priority claim or external human certification was added by this QA.

The checker ran before the parent integrated current main. The parent subsequently reported that all 17 reviewed canonical/submission artifacts remained byte-identical during integration. This report's own evidence is the frozen export below; it does not independently attest the parent's later integration.

PDF text extraction also found zero replacement characters and zero characters outside page bounds. Author detection was checked after removing extraction whitespace and visually; the canonical PDF text extractor sometimes joins adjacent words.

## Frozen artifact hashes

| Artifact | Pages | SHA-256 |
| --- | ---: | --- |
| `linear-systems-and-elimination/IE-02/problem.pdf` | 2 | `528cef7f597c859c7f3c942d1ea3ca55c227c6691e2a589a8801d0d01c46b464` |
| `linear-systems-and-elimination/IE-02/solution.pdf` | 5 | `5c43422fdc05e7cb93862eefb271454988135082976da7a030c61d0044057f2d` |

| Artifact | SHA-256 |
| --- | --- |
| `linear-systems-and-elimination/IE-02/README.md` | `00995b51b7721dba9b969c26d19ebdbf4b9ac494ddc087aef498b570e2ca781d` |
| `linear-systems-and-elimination/IE-02/problem.tex` | `bdd718a5ea1ffebc2c6b520220555097d9d54a61b4171141bda7ae00bfdb3419` |
| `linear-systems-and-elimination/IE-02/solution.md` | `9c9673bdd1e9324c0b4b84519e4691724de67e046b8c17ff3882686cb699d2f9` |
| `linear-systems-and-elimination/IE-02/solution.tex` | `c3bd715724ebd12f95ab75c6b63d420c2efd3132d2e600e4f4e774ee49b8e52a` |

## Integration boundary

Each frozen submission retains its 203-entry historical registry, while fetched current main has 217 entries. Every existing branch ID maps to the same published path. The submitted checker deliberately binds to that historical registry and some global artifacts; it is not a validator for an integrated 217-entry checkout. Preserve the newer published entries during integration, run the repository's base-aware validator and keep the archived checker unchanged. This is an integration caution, not a blocker in the reviewed PDF/source artifacts.

## Evidence and operations

The exact canonical/proof git blobs are exported under `/private/tmp/nla-review-inequalities/pr122-source/`. The machine-readable checks, extracted PDF text and all inspected page PNGs are under `/private/tmp/nla-review-inequalities/pr122-pdf-qa/`, including `snapshot.json` and `checks.json`.

This reviewer changed only scratch exports/evidence/reports. No source, PDF, repository, checker or remote state was edited; the PDFs were rendered to temporary images, never recompiled. No external theorem, historical priority or current network state is independently certified by this packaging review.
