# NR-01: reviewed exact regular-polygon small cases

**Author:** Sidney Holden. **Affiliation:** Center for Computational Biology,
Flatiron Institute, Simons Foundation. Verified on 13 September 2026 against the
[current institutional profile](https://www.simonsfoundation.org/people/sidney-holden/),
which identifies Holden as a Flatiron Research Fellow in Biological Transport
Networks, and the [CCB staff directory](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport&type=ccb-staff).

**Outcome:** The [independent informal Codex AI-agent review](independent-review.md)
passed Theorem 1.1: real nonnegative rank nine for n = 17, 18, 19, 20. The universal
NR-01 target remains **Partially resolved**. This is not external human peer review
or formal verification. No Lean verification was performed.

[Authored manuscript PDF](report.pdf) · [Editable source](report.tex) ·
[Canonical problem](../../nonnegative-and-positive-factorizations/NR-01/README.md) ·
[Original submission and hashes](provenance.md).

The finite theorem covers arbitrary real factors and degenerate lifts. The
argument does not provide a universal recurrence or resolve n=25 (bounds nine
to ten), n=25–30, or n=33–42. The statements concerning the earlier rank-balance
archive are retained in the manuscript as prior work and are outside this
round's independent audit. The original submission is preserved byte for byte.
The authored version corrects proof credit for n=21–24: their lower bound follows
directly from Section 2, combined with the published upper construction.

## Reproduction

From `submitted/`, install `requirements.txt` in a temporary environment, then run:

```sh
python code/verify_all.py --output ../verification-rerun
python code/test_pipeline.py
```

The [full rerun log](verification/verify-all.log),
[summary](verification/summary.json), [regression log](verification/regression.log)
and all per-pattern records are stored in `verification/`. The independent agent
regenerated all 39 spheres and 14,837,760 normal configurations, passed all 13,220
pattern-prime checks, and verified 28 upper factorizations with 17,334 exact entry
identities. The feasible n=16 control was correctly retained. All 13 regression
tests passed. Environment: Python 3.12.14, NumPy 2.3.5, Numba 0.65.1, SymPy 1.14.0.

The separate [reviewer implementation](verification/review-independent-algebra.py)
checks 21 selected patterns using independent elimination and primitive-root
selection. Run it with `python verification/review-independent-algebra.py` from
this directory. Only its input/output paths were adapted for repository portability;
its arithmetic is unchanged and the relocated script was rerun successfully.

## Eligibility and sources

On 13 September 2026, fetched upstream and fork histories, inspected all upstream
pull requests (all states, limit 250; fewer results returned), searched related
issues, and inspected NR-01's history across fetched branches. No previously
pushed full solution for NR-01 or related issue was found. The branch starts at
upstream main `5830ed4fb06da0659414a3deb2a40ad327aca052` and includes only this
submission. No existing problem number, path, or mathematical target is changed.

The current [Baeckelant–Vandaele–Gillis record](https://arxiv.org/abs/2605.14058)
and [v2 Appendix A.2, Table 7](https://arxiv.org/html/2605.14058v2) were checked;
the table records bounds eight to nine for n=17–20. The [published sphere count,
Lutz Table 1](https://arxiv.org/html/math/0604018), confirms 39 eight-vertex spheres.
The [Vandaele–Gillis–Glineur record](https://arxiv.org/abs/1505.08031) supplies the
upper-bound source. Bounded later-result searches located no universal resolution;
this is not a novelty or priority certificate. See the original
[source inventory](submitted/sources.json) and the review's credit correction.
