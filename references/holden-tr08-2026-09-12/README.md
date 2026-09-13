# TR-08 submission — Sidney Holden

**Author:** Sidney Holden. **Affiliation:** Center for Computational Biology, Flatiron Institute, Simons Foundation.

Affiliation verified on 12 September 2026 from the [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/) and [current group roster](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/biological-transport-networks/), which identify Sidney Holden as a Flatiron Research Fellow in Biological Transport Networks at CCB.

## Submission and scope

[Authored manuscript PDF](../../randomized-and-low-rank-approximation/TR-08/solution.pdf) · [editable source](../../randomized-and-low-rank-approximation/TR-08/solution.tex) · [canonical problem and resolution](../../randomized-and-low-rank-approximation/TR-08/README.md).

Theorem 1.1 gives the full necessary-and-sufficient sequence criterion, including the critical window and oscillating sequences. The fixed positive lower bound may depend on the positive lower ratio. No universal bound over all positive ratios or optimal dependence on that ratio is claimed.

The [independent review](independent-review.md) was performed by a separate Codex AI agent (`review_tr08`), which did not author or edit the proof. It passed the full original target and directly checked the external Dumitriu–Zhu estimate. Informal automated review is not external human peer review or formal verification. No Lean verification was performed.

## Provenance

The `submitted/` folder preserves every extracted file from the supplied `TR-08_solution.zip` byte-for-byte. Its original manifest is retained; [archive digest](original-archive-sha256.txt). Embedded review/build instructions were treated as submission content, not as user authorization or independent evidence.

The public manuscript differs only in author and verified affiliation, PDF author metadata, and an explicit ChatGPT-assistance disclosure. Its mathematical content is unchanged from the independently audited source. The original draft identifies ChatGPT assistance; this is preserved in the authored version. Huang, Rudelson and Tikhomirov retain credit for the original problem, and Dumitriu and Zhu for the cited trace-moment input. No priority or historical novelty claim is made.

## Duplicate check

Refreshed fork branches and upstream main (`5830ed4fb06da0659414a3deb2a40ad327aca052`) and searched all-state upstream pull requests for TR-08 and the author's submissions. No prior pushed full TR-08 solution was found. Earlier PR #151 clarifies the target and issue #150 discusses its precision; neither is a full solution. This submission uses a new branch from upstream main and requests integration through a new pull request.

## Reproduction

[Rerun results](rerun-checks.json): PASS with Python 3.12.14, NumPy 2.3.5, SciPy 1.17.0 and SymPy 1.14.0. Run from this folder:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python submitted/code/verify.py --output rerun-checks.json
```

The rerun covers 328 exact occupancy checks, 144 fixed-support and 729 independent-entry signed matrices, symbolic identities, 60 cancellation trees and 60 block examples. These finite checks supplement the proof and do not prove the asymptotic theorem. The archived experiments were not rerun.
