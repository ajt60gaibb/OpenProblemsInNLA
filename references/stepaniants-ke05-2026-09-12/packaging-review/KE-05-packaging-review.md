# KE-05 independent publication-conversion and packaging review

**Verdict: PASS.** The reviewed proof, original target, mathematical scope,
authorship and informal-audit status are faithfully represented in the
prepared KE-05 package. No mathematical or canonical-target correction is
required.

Reviewer: **Codex agent `/root/prepare_manuscripts`**, 12 September 2026 UTC.
This is a separate publication-conversion/source packaging audit. The
complete mathematical audit is the signed report by `/root/review_aa01`;
this report neither replaces it nor claims human peer review or formal
verification. I inspected the prepared worktree read-only and ran the two
exact checkers only in isolated scratch copies. I made no repository,
PDF, git, issue, or PR changes.

## Exact source and original-target preservation

The immutable reviewed manuscript has SHA-256
`51e66685d6e84639ee3aa098ebf1e91e43891c9a6fe04d473f334cf0e6f2a68f`.
The original 4,501-byte canonical README from upstream commit
`1f22006bdaa4659fcaa0bb775a887685cd3cc566` has SHA-256
`ec5086b8ff8215f7445b0c2e185878e09426007d0b721a99b7b814b77e9c065a`.
Both archived copies are byte-identical to these inputs.

The publication's complete mathematical core, from `## Exact target and
conclusion` through the end of Section 5, is byte-identical to the frozen
candidate: **11,073 bytes**, SHA-256
`ead1a59b806a5f47c8f8c5c4a251a8195ebd66bd527ef1653362acd1df8d7bdd`.
All **95 core formulas** and all **98 whole-manuscript formulas** match
the standalone TeX in order, allowing only whitespace and math-delimiter
conversion. I also read the converted TeX prose and scope section; no
hypothesis, constant, implication, qualifier, or probability quantifier
was changed.

The exact original statement and dated history, beginning `Fix integers`
and ending immediately before the original navigation marker, remain
byte-identical in the new canonical README: **3,917 bytes**, SHA-256
`b551a1ec95e4cbd2cd429cb30ade90f68e6c181c902eaa8a3f748725431c9626`.
All **29 canonical-page formulas** match its generated TeX. The permanent
ID and canonical path are retained. The resolution archive change is
additive and leaves prior accepted entries intact.

## Frozen six publication artifacts

The following files are under
`randomized-and-low-rank-approximation/KE-05/`:

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| `README.md` | 6,712 | `244867811efd545f4ffb49f936e0df26452b7f8cb56ba0c51037149b071ed998` |
| `solution.md` | 14,018 | `31c3416ba212cb2cbb73d126633efe79f1e4a2669a80ef5936fa12dc6723bd62` |
| `solution.tex` | 17,050 | `c9e9ef46abae2ad9e70c7fd60d8a5401387bcdc6cdc6be4bf3365d47b6f7262f` |
| `solution.pdf` | 78,587 | `e432e37dd5d046287422e7896d1e892cbb438c050f7e85d202b947e056695ca7` |
| `problem.tex` | 10,202 | `4f3cc37b5e1da5bf180a78094b2030d17a522097aa892c2e6590e4a6ab8ae2ee` |
| `problem.pdf` | 43,236 | `e7a28e4116a68cb954b734117c2b7d913d83dd5a396c87732c410f6af0a935c0` |

## Evidence, links, privacy, and status

The signed independent mathematical review is unchanged, including its
later public-Markdown comparison. The archived original reviewer manifest
matches all seven named inputs after the explicitly documented
`REVIEW.md` to `independent-review.md` filename mapping. The two exact
checkers use only the standard library, locate the adjacent frozen source,
and reproduce their archived JSON exactly when run from an unrelated
working directory in isolated copies. The author's source-filename
adaptation is documented and makes no mathematical change.

I checked the reference README, verification record, portable build and
submission checkers, and all current relative evidence links. The
historical `canonical-statement.md` deliberately retains its original
relative navigation as part of the immutable input; readers should use the
reference README's canonical-entry link for the live documents. The
original 03:13 public-audit files are unchanged. No private raw retrieval
snapshot or third-party full paper is included.

The visible bylines consistently identify George Stepaniants, Department
of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. Shao retains the conjecture and
framework credit. Both current Markdown and TeX sources and all reference
text files passed the contact-email scan. Both PDFs' extracted text and
metadata passed it too, and contain the full name, department and
university.

`Solved` is supported by the repository's explicit rule for a complete
argument with a separate informal audit. The package accurately discloses
substantial AI assistance and does not imply Lean verification, external
human peer review, or acceptance into upstream main. It retains the
interlaced-spectrum/repeated-eigenvalue scope qualification and does not
claim to disprove block Lanczos convergence or an ordered-interval variant.

The final verification record reports 217 preserved IDs against each
published base, 17 ID tests, three status tests, and completed PDF QA. I
checked its artifact bindings. I did not rerun unchanged repository tests
or compile the PDFs. Visual inspection of all five solution pages and both
canonical pages is separately attributed in that record; my additional
PDF check concerns extracted text, metadata and exact file hashes only.

## Final public inventory refresh

At **2026-09-12 03:21:24 UTC**, a fresh recursive fork and public branch
inventory still found **six repositories, 47 heads, and 41 distinct
commits**. There were **no added, changed, or removed heads** relative to
the full 03:13 eligibility snapshot. Upstream main remained
`1f22006bdaa4659fcaa0bb775a887685cd3cc566`. No new source search was needed.
This supplements, rather than rewrites, the earlier source and discussion
audit. It remains a bounded public eligibility check, not a global novelty
certificate.

The separate comparison, metadata, PDF-text and head-refresh JSON records
are supplementary exact evidence. Appending this report and the refresh to
the reference package requires refreshing the outer package manifest;
that metadata-only addition does not alter the six artifact bindings or
any historical signed review.

Signed: **Codex publication-conversion reviewer
`/root/prepare_manuscripts`**, 12 September 2026 UTC.
