# PR #120 MF-22 PDF/source packaging QA

Date: 2026-09-11. Reviewer: Codex agent `/root/audit_inequalities`.

**PASS for read-only PDF/source packaging QA. No packaging blocker found.** This is distinct from the independent mathematical proof review assigned to `/root/audit_trace`.

Frozen PR head: `51e8ae1a801d846f3b649d387e5185df6c4cfdfe`.
Published comparison base (`origin/main` at export): `87366c62d3b5c47d170f747b1cb40ab38d501013`.
Canonical path: `matrix-functions-and-stability/MF-22/README.md`.

## Source identity and target

The six canonical/proof artifacts were exported byte-for-byte from the frozen git head into `/private/tmp/nla-review-inequalities/pr120-source/`. The full original Statement section, through the Numerical significance heading, is byte-identical to the published base. `problem_ids.json` is also byte-identical to that base. MF-22 and its original target are preserved.

The target remains eventual invertibility and a polynomial condition-number bound for each fixed positive parameter in the exact cubic C1 spline Schrodinger block Toeplitz family, without additional corner corrections. The proof's linear bound allows constants and the eventual threshold to depend on the parameter. Its text and PDF include the exceptional parameter rho = sqrt(10), the finite boundary conditions, and the original quantification over every sufficiently large matrix size.

All 145 inline/display mathematical expressions in `solution.md` occur in the same order and agree exactly with their `solution.tex` counterparts after whitespace removal. All 32 expressions in the canonical README similarly agree with `problem.tex`. This is a source correspondence check, not an independent validation of the mathematical claims.

## PDF inspection

All six solution pages and both canonical problem pages were rendered with Poppler to temporary PNG files at a maximum dimension of 1700 pixels and inspected individually. All eight pages pass visual QA: text and displays are legible, with no clipping, overlaps, missing glyphs, or incomplete equations. Text extraction found zero replacement glyphs and zero characters outside page bounds.

The visual review covered the theorem, scalar definitions, recurrence and transfer matrix on solution page 1; generating functions and coprimality setup on page 2; elimination identities and Cayley transform on page 3; discriminant and exceptional-parameter classification on page 4; finite Green cancellation on page 5; and the final norm estimate and attribution on page 6. Both canonical pages preserve the coefficient blocks, Toeplitz definition, complete original question and references. The displays correspond to the Markdown and TeX sources.

| Artifact | Pages | SHA-256 |
| --- | ---: | --- |
| `solution.pdf` | 6 | `de27f0a606bb1415470a6cf3c1cedd4ea5fab6c1075aa7d1e536ffb8b4ae51e9` |
| `problem.pdf` | 2 | `197364dc308c3709c636cce88c4ba5c46ed0638f725f95a89d3a883d5ea01fe8` |

Source SHA-256 values:

- `solution.md`: `a274a6401b27037bb5034cbffe87f02204fdcb663c40a9a7adfe033a19283edb`
- `solution.tex`: `1456bf2df421bb039f33bf32a6f7670975e724a89dd3e885dc946ffe024dd5b7`
- `README.md`: `4d771daf9f3d55299f5e465ceb2dbbc95bc54ddf3f62bc342612139ed1a3ebac`
- `problem.tex`: `fa3faef74b93cf32f7ccb8aecda2147ff81022e274fc2a63a9dad5b19caf3fab`

## Attribution and linked materials

George Stepaniants is consistently identified as the proof's author, with the Department of Computing and Mathematical Sciences at the California Institute of Technology. The canonical page, complete manuscript and linked reference package agree. The package retains credit to Bogoya, Bottcher, Ferrari, Grudsky and Serra-Capizzano for the family, determinant-root classification and original question. It explicitly describes substantial ChatGPT/Codex assistance and distinguishes automated-agent review from external human peer review and formal verification.

The linked reference README and independent review were read at the same frozen head. They describe the complete original target, eventual rather than every-small-size invertibility, and constants dependent on the fixed parameter. All 11 local links in the canonical README and solution Markdown resolve to existing files at the frozen head, including the complete proof, PDF, TeX, independent review and provenance package. This check verifies consistency of attribution and local linkage; it does not independently authenticate the author's affiliation or historical priority.

## Evidence and boundaries

Machine-readable results, extracted PDF text and the eight inspected page PNGs are retained in `/private/tmp/nla-review-inequalities/pr120-pdf-qa/`, including `checks.json`. The exact source export and base README are in `/private/tmp/nla-review-inequalities/pr120-source/`.

No authoritative source or PDF was edited or recompiled. No shared repository files, user worktree files, or remote state were changed. This verdict applies to the frozen head and hashes above; integration and CI are handled by the parent audit task.
