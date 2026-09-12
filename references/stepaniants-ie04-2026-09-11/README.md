# IE-04 submission record — 11 September 2026

**Author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.

**Negative resolution:** the uniform exponential GEPP tail displayed in IE-04 is false. The complete recovered analytic proof passed a separate independent Codex-agent review without a required mathematical correction.

- [Original canonical target](../../linear-systems-and-elimination/IE-04/README.md).
- [Complete proof: theorem, equation (2), and robustness lemma](../../linear-systems-and-elimination/IE-04/solution.md).
- [Standalone proof PDF](../../linear-systems-and-elimination/IE-04/solution.pdf) and [XeLaTeX source](../../linear-systems-and-elimination/IE-04/solution.tex).
- [Supplied source, preserved byte for byte](verification/reviewed-proof.md), and [original-file manifest](verification/original-files.json).
- [Independent complete-proof review](verification/IE-04-independent-review.md).
- [Separate publication-conversion review](verification/IE-04-packaging-review.md) and [exact comparison evidence](verification/IE-04-packaging-comparison.json).
- [Supplied exact interval checker](../../linear-systems-and-elimination/IE-04/verify_bounds.py), [certificate](../../linear-systems-and-elimination/IE-04/certificate.json), and [recorded output](../../linear-systems-and-elimination/IE-04/verification.txt).
- [Separate exact rational checker](verification/IE-04-independent-exact-check.py) and [result](verification/IE-04-independent-exact-check.json).
- [Public eligibility audit](verification/network-check.json), [later refresh](verification/network-before-push.json), and [read-only reproduction script](verification/network_check.py).
- [Original canonical page](verification/original-target.md), [portable source checker](verification/check_submission.py), [source-check result](verification/source-checks.json), and [document verification record](verification/document-checks.json).

## Exact result and scope

For every $n\ge2$, a full entrywise box around an explicit high-growth matrix consists of nonsingular matrices with strict partial-pivoting choices and growth greater than $(3/2)^{n-1}/2$. For $A=I_n+G$, that box has probability at least $2^{-n^2(n^2+n+5)}$. Given any proposed universal $c_1,c_2>0$, setting $x=(3/2)^{n-1}/(2n^{c_1})$ violates the displayed exponential upper bound for sufficiently large $n$.

The proof uses the exact real Gaussian model, the original active-Schur-complement growth convention, a deterministic nonsingular center of spectral norm one, and an allowed noise level. It does not replace the target with a restricted range of $x$, a changed pivot rule, or a different growth normalization. A sharp replacement smoothed tail and high-probability polynomial exponent are outside this result.

The primary historical statement is Spielman–Teng, *Smoothed Analysis of Algorithms and Heuristics: Progress and Open Questions*, Section P6, Conjecture 16, page 52 of the [author PDF](https://www.cs.yale.edu/homes/spielman/PAPERS/focmSmoothed.pdf), DOI [10.1017/CBO9780511721571.010](https://doi.org/10.1017/CBO9780511721571.010). The independent review checked that page visually. The precisely quantified canonical repository statement is the target certified here.

## Authorship, assistance, and preserved source

The proof was developed with substantial ChatGPT/Codex assistance at the author's request and completed in the supplied recovery archive. The publication adds author metadata, completed-review status, and page-layout directives. The complete mathematical argument is preserved. Automated discovery and separate automated-agent review are distinguished; no external human peer review, formal proof-assistant certification, or novelty/priority determination is claimed.

The supplied `solution.md` has SHA-256 `428c586bf6a0b66ce94d478eed5be6e951032cc09fc646df7204ae2823b14a75`. Every supplied IE-04 file is retained unchanged in `originals/`; its preparation-stage wording is historical. The signed independent review has SHA-256 `757daf1061629d1b1efbebc1a8546fca0a2dfb339d2a8e8d68237a08ccd48564`. It reconstructs the all-dimension elimination and perturbation argument, the Gaussian lower bound, and the contradiction for arbitrary real constants.

The supplied standard-library checker was read and rerun successfully; its output certificate matches the preserved certificate byte for byte. A separate reviewer-written rational GEPP checker verifies unperturbed cases through order 24, every box corner in orders two and three, and scalar bounds through order 512. Those finite checks are supplementary; the analytic induction certifies the entire box in every dimension.

## Eligibility and repository procedure

At 23:46:05 UTC on 11 September 2026, the public-network audit covered five repositories, all 33 public branch heads, 156 distinct relevant text documents, and 26 PR review bodies, together with matching issue/PR bodies and comments. Every canonical IE-04 page was Open. Nine discussion matches concerned other problems and contained no IE-04 resolution. The sanitized snapshot preserves all target-specific canonical versions and an inventory of scanned documents.

The refresh at 23:51:45 UTC covered the same five repositories and 33 heads, 176 distinct text documents, and 26 PR review bodies. All IE-04 pages remained Open; the only recorded discussion match concerned unrelated regularization work. No full IE-04 resolution was found. Private, deleted, unpublished, or unidentifiably named work is outside these bounded checks. The reproduction script uses GitHub CLI via `GH` or `PATH`, reads the registry relative to itself, accepts optional hash-verified caches only when supplied, and requires an explicit output path. It makes no public mutation.

This isolated branch starts directly at upstream `main` commit `87366c62d3b5c47d170f747b1cb40ab38d501013`. It retains the canonical path, complete original mathematical target, historical ratings, and all 203 permanent ID mappings. The intended submission is a correction-or-resolution issue and a new pull request into upstream `main`; maintainer review is requested, without self-merging.

Render with `python3 tools/render_solutions.py IE-04` and `python3 tools/render_problems.py IE-04`, using Pandoc and XeLaTeX. The resulting TeX files are standalone. The optional-email template conditional prevents an omitted contact field from creating an empty email link. Exact validation and visual-inspection results are recorded in the document verification record.

Both permanent-ID validators pass against `origin/main` and `upstream/main`, preserving all 203 mappings, and all 17 safeguard tests pass. The source checker verifies the unchanged 6,168-byte mathematical core and all 92 ordered mathematical expressions in its generated TeX. All four solution pages and both canonical pages were visually inspected after successful two-pass builds. A separate publication-conversion reviewer independently confirmed the entire core, all 95 mathematical expressions including the verification section, the complete original Context-through-history suffix, and all six PDF pages. Its signed PASS has SHA-256 `5730e760dd6b37072170e98fbcbdae862b02a2bf92ef57d3b20050c026ae5fde`. This packaging step performed no commit, push, issue creation, or pull-request creation.

## Integration with the published main branch

On 12 September 2026 UTC (11 September locally), the reviewed submission was merged with published main `bfaa1d0675f24011e42740d48ea6966f83bb1bff`. The [integration check](verification/upstream-integration-bfaa1d0.json) preserves all six reviewed canonical artifacts and all incoming reference files byte for byte, including accepted resolutions and 14 newly appended IDs. All 217 current IDs validate against the published base; all 17 safeguard tests pass. The original 203-entry source check now compares each permanent mapping, permitting later append-only entries while the repository validator checks the complete current registry. No mathematical source, target, PDF, signed review, or historical check record was rewritten.

A [final public-network refresh](verification/network-final-publication.json), completed at 00:22:17 UTC on 12 September 2026, found IE-04 still Open on every one of 35 branch heads across five public repositories. It read 196 distinct selected text blobs and 32 PR review bodies. Matching new IE-05 and SP-11/SP-12 records are this author's separate submissions; the remaining IE-08 match concerns a different target. No prior full IE-04 resolution was found within the stated public-search scope.
