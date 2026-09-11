# Additional eigenvalue and inverse-problem submissions

This package contains **one proposed full resolution of a repository entry and one explicit-family partial result**. It does not replace or re-count the earlier two submission packages.

| Entry | Scope | Reported status |
|---|---|---|
| IE-10 | Full cyclic-shift, complex-sphere target; proposed constants C = 1700, c = 3 | Solution claimed, pending independent mathematical review |
| IS-04 | Explicit odd prime-square family; not every dimension | Partial progress; retain Partially resolved |

The IS-04 manuscript additionally addresses Problem 13 in the source paper, a separate explicit-family question. It does **not** resolve that paper's Problem 12, which is the repository target. All manuscripts disclose AI generation, absence of independent refereeing or formal verification, and lack of a priority claim.

## Submit two separate GitHub issues

1. Read the relevant manuscript and the scope statements. Check the repository for an existing issue or later result before posting.
2. Open the repository's [Correction or resolution issue template](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/new?template=correction_or_resolution.md).
3. Copy the corresponding `issues/ID-title.txt` into the title field. Paste the **contents** of `issues/ID-issue.md` into the body, replacing the template prompts. Do not paste a local filename or a link to this chat as the evidence.
4. Attach the matching PDF from `manuscripts/`. The reports contain the full proofs already, so they remain self-contained even without an attachment. Optionally attach `attachments/verification-support.zip`.
5. Preview the mathematical formatting, keep the status and uncertainty language accurate, and submit. Repeat for the second report.

A GitHub account is needed to post. No Git installation, repository clone, or LaTeX installation is required for the issue route. Attachments and issue text in this public repository should be treated as public material.

## Which files go together?

| Issue | Text to paste | PDF to attach |
|---|---|---|
| IE-10 | `issues/IE-10-issue.md` | `manuscripts/IE-10-proposed-resolution.pdf` |
| IS-04 | `issues/IS-04-issue.md` | `manuscripts/IS-04-explicit-odd-family-partial.pdf` |

The Markdown and standalone LaTeX manuscripts are also supplied. The proof PDFs are separate manuscripts, **not replacement copies of the repository's `problem.pdf` files**.

## Review and reproducibility

Start with `VERIFICATION_SUMMARY.md`. The complete recorded diagnostics and code are in `verification/`, with execution instructions in `verification/README.md`. They distinguish exact symbolic/integer checks from floating-point tests. The probability theorem and the classical mixed character-sum estimate are not proved by those tests.

`RESEARCH_SCOPE.md` identifies the other entries considered without claiming resolutions. `sources/SOURCE_MANIFEST.md` records the primary mathematical and repository sources and their precise uses. `REVIEW_CHECKLIST.md` lists points for an independent reviewer to check.

This is an **issue-submission package**, not a ready-to-merge repository patch. A subsequent catalogue pull request should retain the original ID and statement, add the dated result with the correct verification status, and follow the repository's regeneration instructions. Nothing has been posted to GitHub.
