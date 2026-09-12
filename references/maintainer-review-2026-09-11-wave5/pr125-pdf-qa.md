# PR #125 SP-11 and SP-12 PDF/source packaging QA

Date: 2026-09-11. Reviewer: Codex agent `/root/audit_inequalities`.

**PASS for PDF/source packaging. No packaging blocker found.** Mathematical correctness and final integration are independently reviewed by the parent and other agents.

Frozen reviewed PR head: `96c83a5e5c4be73194f47d01e68a0a8f2a062e87`.
Current published target-comparison base: `b8e255ccc2d51671714241ff6c3eba29d1d70f41`.

## Inspection and consistency

All ten PDF pages were rendered with Poppler to separate temporary PNGs at maximum dimension 1700 pixels and inspected individually. SP-11 has two canonical pages and two solution pages; SP-12 has three canonical pages and three solution pages. No clipping, overlap, missing glyph, broken equation or unreadable attribution was found. Each canonical document displays the current resolution, original statement, exact hypotheses and historical sources/status checks. The complete application notes retain their external theorem locators, deduction, scope and attribution. Page numbers and transitions are legible.

All mathematical expressions agree in Markdown/TeX, in order and exactly after whitespace removal: SP-11 has 19 solution and 16 canonical expressions; SP-12 has 98 solution and 20 canonical expressions, for 153 total. The source comparison covers every inline and display expression. For both canonical entries, everything beginning at the original Problem statement section is byte-identical to published main `b8e255ccc2d51671714241ff6c3eba29d1d70f41`, including references and historical status checks. The original unrestricted real-symmetric SP-11 target and PSD/SAP SP-12 target remain distinct and unchanged.

The submitted `references/stepaniants-sp11-sp12-2026-09-11/verification/check_submission.py` was read before execution. It uses only standard-library local reads; it performs no network or filesystem mutation. Running it with `python3 -B` at the reviewed head returned PASS: six reconstructed original-package files, five supplied checksums, two original targets, all formula sequences, 18 source-checkpoint artifacts, 203 original IDs and all submission-local links passed. Independently, all 18 byte lengths and hashes in `source-checkpoints.json` match the frozen checkout.

The PDFs, canonical pages and application notes consistently credit H. Tracy Hall for the essential all-graph theorem and George Stepaniants for the explanatory application notes. Theorem 3.20 and the relevant corollaries are clearly identified. The publications retain the distinction between the preprint's mathematical theorem and the new notes' application, explicitly disclaim a new discovery/priority claim, preserve the withdrawal of unsupported prior artifact/graph-atlas assertions, and disclose AI assistance and agent-review limits. These attribution statements are consistent within the inspected package; independent proof/source verification is assigned to the other mathematical auditors.

PDF text extraction also found zero replacement characters and zero characters outside page bounds. Author detection was checked after removing extraction whitespace and visually; the canonical PDF text extractor sometimes joins adjacent words.

## Frozen artifact hashes

| Artifact | Pages | SHA-256 |
| --- | ---: | --- |
| `eigenvalues-and-inverse-problems/SP-11/problem.pdf` | 2 | `da4c2f17a1c170203ec6f01d6453b3b6c185a5b42503d6798a9e7c3b125f779c` |
| `eigenvalues-and-inverse-problems/SP-11/solution.pdf` | 2 | `c6b34469d2de152a9deb5cb62e76d6b21370364ab3d98e7fdfc745920e99468b` |
| `eigenvalues-and-inverse-problems/SP-12/problem.pdf` | 3 | `a840bd5f08dd70f8fd6098e3bab54fed1e9e9424bc3d4207b6c24973976b9f2e` |
| `eigenvalues-and-inverse-problems/SP-12/solution.pdf` | 3 | `63056390494e76bd4932705ae84051f229134600a8e59564aace70bcb202dc9d` |

| Artifact | SHA-256 |
| --- | --- |
| `eigenvalues-and-inverse-problems/SP-11/README.md` | `b47c87d3e05969234432e9b91c1b20a2e1f0a40f31bfdc45ff46467f69444859` |
| `eigenvalues-and-inverse-problems/SP-11/problem.tex` | `39d92a454b73abca3d15a7e9e34f56efeb1a63149ec78bca4dc49a78c5f6fe1e` |
| `eigenvalues-and-inverse-problems/SP-11/solution.md` | `87bc90a768d9d9910a4f4b041cee46f3821b9c7dfe89eec3c2b49b92a1a15253` |
| `eigenvalues-and-inverse-problems/SP-11/solution.tex` | `a639991609d402f107035c9e970519273237dd4fee838bd91ee23a0ba71ac0d8` |
| `eigenvalues-and-inverse-problems/SP-12/README.md` | `ad8b6d4a0521a298fb6c763c9b53dc6b4bbee414a394abcc98bd3cf8e3d07b47` |
| `eigenvalues-and-inverse-problems/SP-12/problem.tex` | `4503a3c2b0d836fa6fa901ddf70ddcd1dbfe825402cc77d18758877ec8dfaebb` |
| `eigenvalues-and-inverse-problems/SP-12/solution.md` | `b3ec241b74a4b106a817f5dfef85873cd0166c394c876c6a89b201d61eaee690` |
| `eigenvalues-and-inverse-problems/SP-12/solution.tex` | `9ee16a9824a231e8cacde3c76062eae16b387c9965b64223828ea043f910c170` |

## Integration boundary

Each frozen submission retains its 203-entry historical registry, while fetched current main has 217 entries. Every existing branch ID maps to the same published path. The submitted checker deliberately binds to that historical registry and some global artifacts; it is not a validator for an integrated 217-entry checkout. Preserve the newer published entries during integration, run the repository's base-aware validator and keep the archived checker unchanged. This is an integration caution, not a blocker in the reviewed PDF/source artifacts.

## Evidence and operations

The exact canonical/proof git blobs are exported under `/private/tmp/nla-review-inequalities/pr125-source/`. The machine-readable checks, extracted PDF text and all inspected page PNGs are under `/private/tmp/nla-review-inequalities/pr125-pdf-qa/`, including `snapshot.json` and `checks.json`.

This reviewer changed only scratch exports/evidence/reports. No source, PDF, repository, checker or remote state was edited; the PDFs were rendered to temporary images, never recompiled. No external theorem, historical priority or current network state is independently certified by this packaging review.
