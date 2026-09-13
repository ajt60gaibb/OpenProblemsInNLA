# NM-01 round-two partial results — Sidney Holden

**Author:** Sidney Holden. **Affiliation:** Center for Computational Biology, Flatiron Institute, Simons Foundation.

Affiliation verified on 13 September 2026 using the [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/) and [current CCB staff roster](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport&type=ccb-staff). They identify Holden as a Flatiron Research Fellow in Biological Transport Networks.

[Authored manuscript](nm01_round2.pdf) · [LaTeX source](nm01_round2.tex) · [Independent informal AI-agent review](independent-review.md) · [Canonical target](../../nonnegative-and-positive-factorizations/NM-01/README.md).

## Scope

Theorem 2.3 gives conditional factor recovery on the stronger SSC subclass using an exact decision/value oracle; it does not construct that oracle. Theorems 3.1–3.2 establish weak-SSC rigidity and an explicit interval of projective probes outside the whole original promise. Theorem 4.5 and Corollary 4.7 obstruct bounded-degree input-preordering certificates and polynomial-size standard dense SOS levels. They do not rule out other polynomial algorithms, general SDPs or sparse lifts. The full original rational-input decision problem remains open. The separate informal review is evidence for these partial scopes only; no Lean verification was performed.

## Provenance and eligibility

`submitted/` preserves every delivered archive file byte for byte, including the first-round archive and the original author/disclosure text. Its manifest can be checked with `python3 submitted/code/check_manifest.py`. The authored manuscript changes only attribution, affiliation, PDF author metadata and the review/disclosure notice; the mathematical body is unchanged. Prior mathematical sources retain their attribution. The submitted historical status reports are preserved as supplied; the linked independent review records the later audit. No novelty or priority certification is asserted.

The duplicate check on 13 September 2026 inspected NM-01 at 43 fetched origin/upstream remote refs (including the origin HEAD alias), all of which retained Open status; see [branch evidence](eligibility.json). The upstream all-state pull-request search for NM-01 returned only PR #40, which addresses other factorization problems and does not submit a full NM-01 solution. This bounded check found no previously pushed full NM-01 solution; it does not cover private, deleted or unpublished work. This new branch starts at upstream main `5830ed4` and changes no permanent ID or original target.

## Reproduction

Run from `submitted/` with Python and SymPy 1.14.0:

```sh
python3 code/check_manifest.py
python3 code/test_round2.py --full --report /tmp/nm01-round2-tests.json
```

The independent review records the commands actually rerun and their results. Supplied historical logs remain under `submitted/verification/`. Compile the authored manuscript twice with `pdflatex -interaction=nonstopmode -halt-on-error nm01_round2.tex`.

Submission checks: all 53 original manifest files verified; 23 full-suite test methods passed with no skips; reviewer-written rigidity checks and additional SOS cross-checks passed. All 217 permanent IDs validate and all 17 safeguard tests pass. Mathematical body and original canonical target are unchanged. The rebuilt 19-page manuscript and 3-page canonical PDF were visually inspected. See [verification](verification/submission-checks.json). Status remains **Open** under the repository's precise definition: no new decision subclass is settled by this round.
