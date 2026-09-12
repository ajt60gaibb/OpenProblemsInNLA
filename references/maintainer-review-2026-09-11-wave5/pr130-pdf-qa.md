# PR #130 IE-04 PDF/source packaging QA

Date: 2026-09-11 local. Reviewer: Codex agent `/root/audit_inequalities`.

**PASS for PDF/source packaging. No artifact blocker found.** The new renderer membership is sound; preserve later main renderer/template changes during integration. Mathematical correctness and final integration are separately assessed by the parent and mathematical auditor.

Frozen reviewed head: `397c70a40e8ee785201800d20f798c7d9b73c22f`.
Current published target-comparison base: `1f22006bdaa4659fcaa0bb775a887685cd3cc566`.
PR branch merge base: `bfaa1d0675f24011e42740d48ea6966f83bb1bff`.
Canonical path: `linear-systems-and-elimination/IE-04/README.md`.

## All-page visual inspection and formula correspondence

The two canonical PDF pages and four solution PDF pages were rendered with Poppler to separate temporary PNGs at maximum dimension 1700 pixels and inspected in full. All six pass: no clipping, overlaps, missing glyphs, incomplete equations or illegible quantifiers were found. PDF extraction found zero replacement characters and zero characters outside page bounds. Both documents visibly identify George Stepaniants and the Caltech affiliation.

The first canonical page retains the complete growth normalization, pivot/tie convention and original uniformly quantified statement. The range covers every dimension, deterministic real center with spectral norm at most one, every permitted positive noise level at most one and unrestricted x at least one. The negative-resolution notice displays the lower probability bound and the admissible choice of identity center and unit noise. References and earlier status checks remain legible on page 2.

The solution's four pages display the original universal inequality, precise all-dimension lower bound, explicit piecewise matrix and order-four example, strict pivot choices, quantitative full-box robustness estimates, Gaussian box probability and contradiction for arbitrary positive constants. The unrestricted x range is preserved throughout. The proof distinguishes the deterministic center from the center of the high-growth event and distinguishes finite exact checks from the analytic universal argument. Scope, provenance and references are complete on page 4.

All 95 mathematical expressions in the complete solution Markdown and all 23 canonical expressions agree with generated TeX, in order and exactly after whitespace removal. The count includes the verification section, in addition to the 92 expressions within the mathematical core checked by the submitted checker. This correspondence check does not itself certify the mathematical inequalities.

## Target, raw package and checker

Everything from the original Context and notation heading through the canonical references and history is byte-identical to current published main. The target, ID and path have not been replaced or narrowed.

All seven raw supplied files in `references/stepaniants-ie04-2026-09-11/originals/` match the recorded byte lengths and SHA-256 values in `verification/original-files.json`. The raw proof source also matches the frozen reviewed proof. The canonical checker, certificate and recorded verification output remain byte-identical to their raw supplied counterparts. The supplied certificate rerun matches the preserved certificate.

`check_submission.py` was read in full before running `python3 -B`. It performs local reads plus read-only `git show` and `pdftotext` calls; it does not invoke the mathematical checker, write source files or access the network. It returned PASS with 1,112 valid local links, seven preserved supplied files, the frozen proof/review/conversion-review hashes, the unchanged 6,168-byte core after specified layout/heading normalization, and the complete original target/history. Its output is retained in `pr130-pdf-qa/submitted-checker.json`.

The checker correctly treats the original 203 ID mappings as a preserved subset and permits later appended entries. This branch has 217 entries, with exactly the same ID/path mappings as current main. It does not weaken the repository's separate full-registry validation against the published base.

The dated original `document-checks.json` is a pre-integration record: 30 file hashes still match, including every canonical and raw supplied artifact. Eight later-changed files are the shared indexes, renderer/template, appended reference README and append-aware checker. Those differences are documented by the package's integration note and are not changes to the reviewed mathematical source or PDFs; the historical record was retained rather than presented here as a current global fingerprint manifest.

Attribution is consistent: George Stepaniants is identified as author of the recovered proof; Spielman and Teng retain the historical motivation/source attribution. The proof explicitly limits its resolution to the precisely quantified canonical tail inequality and does not claim an optimal replacement tail or resolve a separate high-probability polynomial bound. AI assistance and automated-review limits are disclosed.

## Renderer change and integration boundary

Relative to its branch merge base, the only renderer change adds the literal `IE-04` to the existing set of identifiers whose References subsection receives a page break. Removing that single set member makes the Python AST identical to the base renderer. The change therefore leaves the other identifier branches intact and only separates IE-04's references/history from its retained target.

Current main is newer than that branch base. Preserve its IE-05 layout branch, IE-01 reference break, SP-11/SP-12 target breaks and conditional solution-table support when integrating. Add only IE-04 to the current reference-break set; do not replace the current renderer or solution template wholesale with the older branch copies. The parent was notified of this reconciliation requirement. No rebuild or repository edit was performed in this QA.

## Frozen canonical hashes

| Artifact | SHA-256 |
| --- | --- |
| `README.md` | `4dc92888b019c4b4816e891fab15377128415f2e2caa9b44e4cdc7973e34050a` |
| `problem.pdf` | `2774d9c462d6fd6df8ee748ff42c30cf787716ecde94b093ef601e2e945febff` |
| `problem.tex` | `06f4e51a63a43841cd41c80d99e75bfe71b7e47e540aada370a62fba2166f59a` |
| `solution.md` | `5418bb8fa765313d2e4dcbd85a78558e244fc6207b165b511a2b03532f34199e` |
| `solution.tex` | `e776df45e852467d1e9f27674dbd85fc9cd3c06fb5ec7a3760bb146bf9a8d4c6` |
| `solution.pdf` | `f0857c8559155d840343639b4930e3fb842d9c08baec6e5898fed42088a29ac3` |

The canonical PDF has two pages and the solution PDF has four.

## Raw seven-file package hashes

| Original supplied file | SHA-256 |
| --- | --- |
| `certificate.json` | `535884c66752361d166ea5b40063ea126689bc269353441ead2040ba688bde09` |
| `solution.md` | `428c586bf6a0b66ce94d478eed5be6e951032cc09fc646df7204ae2823b14a75` |
| `solution.pdf` | `2c76de236225a7e1fe95fed2dbe969934c26b2ff5b02de9685e1b1493a9ff941` |
| `solution.tex` | `0c9d28e3a3c3ad880affd5be614ebbfbb698d33fc05f42b19e8e119d923e6877` |
| `submission.md` | `b29597f49373a5429ba7734a41523934aac9f85caa2099c29d206c562471a735` |
| `verification.txt` | `0b80bd490e1be6872b227fbca32cb7bf4238fc189963b1c2d690538f3535d334` |
| `verify_bounds.py` | `f08cebc9bc2a8fe28f53c2033da0c5d56c16b80f21b4055d3eb460f9dc68ea14` |

## Evidence and operations

Exact canonical/proof git blobs are exported under `/private/tmp/nla-review-inequalities/pr130-source/`. Machine-readable results, source/checker evidence, extracted text and all six inspected page PNGs are in `/private/tmp/nla-review-inequalities/pr130-pdf-qa/`, including `snapshot.json` and `checks.json`.

This reviewer wrote only scratch snapshots, renderings and evidence. No authoritative PDF, canonical source, checker, repository or remote state was edited. This verdict applies to the frozen head above and does not independently certify later integration, current network status or historical priority.
