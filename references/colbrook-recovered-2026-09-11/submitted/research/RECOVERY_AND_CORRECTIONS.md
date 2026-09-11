# Recovery record and corrections

## What was recovered

The filesystem was empty when this reconstruction began. Mathematical text and verification-code descriptions were recoverable from the earlier conversation record. Those materials were used to reconstruct seven self-contained proof notes covering eight candidate results, plus a partial rook-pivoting matrix family. The PDFs, Markdown files, test outputs, and ZIP in this release are newly created files. This is not a bit-for-bit restoration of an earlier archive.

The exact-rational verifier has been executed in this reconstruction. Its new output, rather than an earlier reported pass, is included in `verification/results.json` and `verification/verification_log.txt`. The rook family has a separate exact check and output. The proof notes retain the mathematical arguments, while unsupported statements about source access and resolution status have been removed or qualified.

## Corrections made during reconstruction

The recovered LSMR text assigned the following incorrect exact fraction to the first upper witness's quadratic form:

$$\frac{2715630211217370564}{2832608020933442045}.$$

The exact computation instead gives

$$u^T D u=\frac{1642993919237}{1713779258646}.$$

The proof note uses the corrected fraction. It remains strictly below $1979/2000$, so the upper certificate and the strict separation from $99/100$ are unchanged. The verifier also checks the explicit rational perturbation and the positive principal minors directly.

The row-deletion supremum statement has been written explicitly with its normalization, namely the supremum of $\sqrt{n/m}\,s_\theta(A)$, to remove an ambiguity in the recovered wording.

The Anderson pairwise expression is used only when its denominators are nonzero. Every displayed example meets that condition. The finite-step result is explicitly separated from asymptotic convergence.

For the rook family, $t=1/6$ is a newly selected rational specialization of the recovered formula; its certificate was generated and checked in this reconstruction. It is not presented as a recovered sharp theorem.

## Items not recovered or not established

No original repository checkout, original-source snapshots, verified commit identifier, complete exploratory search history, or prior ZIP bytes were present. No third-party full-text papers are included. Some earlier references use conflicting problem identifiers. The local IE labels are therefore provisional, and the precise formulations printed in the notes take precedence over an unverified mapping to the repository.

The earlier claim that a completed submission archive had already been delivered was incorrect. This package makes no claim of three hours of uninterrupted active work. No result has been independently peer reviewed, formally verified by a proof assistant, accepted by the repository, or checked comprehensively for novelty.

The earlier summaries' additional small-order rook upper-bound proof and some higher-order experimental results were not recovered as complete, verifiable arguments. They are not silently replaced with invented results. Other unresolved problems in the repository are not counted as solved.

## Assistance and submission status

The notes and software were developed and reconstructed with substantial AI assistance. That disclosure should accompany any submission. No author identity has been invented. No email, GitHub issue, pull request, or paper has been submitted externally as part of this reconstruction.
