# IE-02 submission record — 11 September 2026

**Author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.

**Affirmative resolution:** ideal and worst-case GMRES agree for every single Jordan block in the exact complex model of IE-02. The complete proof passed a separate independent Codex-agent review with no correction required.

- [Original canonical target](../../linear-systems-and-elimination/IE-02/README.md).
- [Complete proof, Theorem 1](../../linear-systems-and-elimination/IE-02/solution.md), with the stronger affine triangular-Toeplitz result in Theorem 6.
- [Standalone proof PDF](../../linear-systems-and-elimination/IE-02/solution.pdf) and [XeLaTeX source](../../linear-systems-and-elimination/IE-02/solution.tex).
- [Frozen research source](verification/reviewed-proof.md), preserved byte for byte.
- [Independent complete-proof review](verification/IE-02-independent-review.md), bound to the frozen source.
- [Separate publication-conversion review](verification/IE-02-packaging-review.md), bound to the final source and PDFs.
- [Primary-source and scope audit](verification/source-audit.md).
- [Public-network eligibility snapshot](verification/network-check.json) and [read-only reproduction script](verification/network_check.py).
- [Original canonical page](verification/original-target.md), before this submission.
- [Portable source checker](verification/check_submission.py), [source-check result](verification/source-checks.json), and [document verification record](verification/document-checks.json).

## Exact scope

The result covers all $n\ge2$, $1\le k<n$, and $\lambda\in\mathbb C\setminus\{0\}$, with complex polynomials satisfying $p(0)=1$ and complex unit starting vectors. It imposes no divisibility, singular-value simplicity, or eigenvalue-regime assumption. The matrix is the original single Jordan block, without doubling, additional blocks, or a changed norm.

The proof represents the extremal triangular Toeplitz residual as a compression of a finite Blaschke multiplier. Its maximal singular vectors have a common polynomial factor. Scalar spectral factorization then turns the finite convex combination supplied by norm optimality into one vector preserving every complex GMRES orthogonality equation. The only external analytic input is the classical finite Carathéodory–Fejér theorem, cited precisely as Theorem CF, Section 2, page 84 of Courtney–Sarason (2012).

## Authorship, assistance, and review

This proof was developed with substantial ChatGPT/Codex assistance at the author's request. Automated discovery and independent automated-agent review are distinct. No external human peer review, formal proof-assistant verification, or exhaustive priority determination is claimed.

The frozen proof has SHA-256 `64bbb398344d56651a1a59c65613817bc932cea6772483893a5fc195ce3d9fb9`. Sections 1–5 of the publication manuscript preserve the complete mathematical argument, allowing only explicit layout directives. The frozen source's preparation-stage wording is retained as history; the publication metadata records the eventual review result separately.

## Repository procedure

The branch is based directly on upstream `main` at `87366c62d3b5c47d170f747b1cb40ab38d501013`. It retains the canonical IE-02 path, every original target quantifier, and all 203 permanent ID mappings. The original ratings are retained as historical assessments. The intended submission uses the correction-or-resolution issue format and a new pull request into upstream `main`; no self-merge is requested.

Render with `python3 tools/render_solutions.py IE-02` and `python3 tools/render_problems.py IE-02`, using Pandoc and XeLaTeX. Both generated TeX files are standalone. The optional-email template conditional prevents an omitted contact field from creating an empty mail link.

## Eligibility and verification

At 23:25:40 UTC on 11 September 2026, the public-network audit covered five repositories and all 32 public branch heads, 114 distinct relevant text files, and 26 PR review bodies, along with matching issue/PR bodies and comments. Every canonical IE-02 page was Partially resolved, and no full resolution or matching discussion was found. The snapshot retains target-specific evidence and hashes of unrelated scanned files. Private, deleted, unpublished, or unidentifiably named work is outside this bounded audit.

The independent proof review is preserved unchanged with SHA-256 `5a7f2e3b9f28d16566da3e51046434c889ad7cec686ad083e6250597fc951e6c`. It independently checks the precise primary CF theorem, the scalar factorization, the full maximal singular subspace, simultaneous preservation, complex separation, affine minimization, and every target endpoint. It returns PASS without relying on numerical evidence.

The permanent-ID validators pass against both `origin/main` and `upstream/main`, protecting all 203 mappings. All 17 safeguard tests pass. The source checker confirms the unchanged 9,153-byte mathematical core and all 157 ordered TeX expressions, the original target, and all checked local links. All five solution pages and both canonical pages were visually inspected after successful two-pass XeLaTeX builds. A separate root-agent publication-conversion review returned PASS after independently comparing the complete mathematical core, every original target and historical suffix, rerunning the source checker, and inspecting all seven PDF pages. The signed addendum has SHA-256 `1b1ddb76a4c6bf1e38ae43fd3ea16edaff4daebb8568e59d760dcce8e0c087e0`. No commit, push, issue, or pull request has been created by this packaging step.
