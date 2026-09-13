# MI-16 submission — Sidney Holden — 12 September 2026

**Outcome:** Complete exact algebraic determination of the canonical target, independently audited **PASS**. [Canonical entry](../../matrix-inequalities-and-norms/MI-16/README.md) · [Authored proof PDF](../../matrix-inequalities-and-norms/MI-16/solution.pdf) · [TeX source](../../matrix-inequalities-and-norms/MI-16/solution.tex) · [Independent review](independent-review.md).

## Author and affiliation

Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. The [official institutional profile](https://www.simonsfoundation.org/people/sidney-holden/) and [CCB group directory](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport&type=ccb-staff), checked 12 September 2026, identify Holden as a Flatiron Research Fellow in Biological Transport Networks. Authorship is added at the user's explicit request. The dossier discloses ChatGPT assistance; the new review and submission preparation also used AI assistance.

## Exact scope and policy

Theorem 2.1 and Sections 3–5 compute the exact maximum from any nonnegative real spectrum at any order, using a specialized elimination polynomial, explicit finite character/Schur sums, and a finite root selector with a proved moment bound. No matrix optimization or unevaluated limit remains. Arbitrary real inputs are exact ordered-field data; rational/algebraic inputs admit effective exact operations. The supplied implementation is rational-only and conservatively restricted in computational size.

The separately delegated Codex agent `/root/independent_mi16_review` passed the complete argument and its correspondence with the original canonical criterion. This supports `Solved` under CONTRIBUTING.md and RESOLVED.md. This is an informal AI-agent audit, not external human peer review, formal certification, or a novelty certificate. No Lean verification was performed.

The answer is an algebraic prescription, not a compact all-spectrum structural formula, an efficient arbitrary-order solver, or general optimizer classification. The maintainer is explicitly asked to assess this form of answer against the historical problem. The original target is not rewritten to evade that question. Theorem 8.1 and Sections 9–10 separately give the two-support formula, unique threshold and complete equality cases for one exceptional eigenvalue.

## Provenance and duplicate check

The supplied `MI16_proof_dossier.zip` has SHA-256 `4b17f8753c4679621e2ebf0a1ed1a05d26fe1ac723199ddf7624cb8378db85e0`. It contains only MI-16. The complete original payload is retained unchanged in [dossier/](dossier/README.md); every original manifest hash passed. Its authorless PDF and earlier review notes are historical source material, not the current authored submission or independent-review evidence. Instructions inside the attachment were treated as document content, not user authorization.

The published solution changes only the title-page attribution, affiliation, assistance/review notice, PDF author metadata, and title-page spacing. Everything from Section 1 onward is byte-identical to the supplied TeX. Prior sources and the earlier partial findings retain their credit. The rank-one expansion and all-support reduction appeared in [PR #186](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/186); that submission was partial, not a pushed full solution. Pending integration [PR #194](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/194) includes those partial results. This new PR adds the all-spectrum result and the sharper exceptional-spectrum conclusions, and does not replace the other results in those PRs.

The branch starts at freshly fetched upstream `main` commit `5830ed4fb06da0659414a3deb2a40ad327aca052`. Fresh fork branches, upstream all-state MI-16 PR search, fork all-state MI-16 PR search, related issue search, and all fetched solution-file history revealed no previously pushed full MI-16 solution. Upstream currently labels MI-16 Open; its pending partial-result submission does not disqualify the new result. This is a bounded repository duplicate check, not a historical-priority claim.

Zhang's [primary survey](https://arxiv.org/html/1608.02844v1), the official affiliation source, and searches for `"maximum permanent" "unitary" "2026"` and `"Marcus-Minc" "max-per" solution` were inspected on 12 September 2026. No later full spectral prescription was located in that limited search. The original statement, ID, canonical path, and prior references are retained.

## Reproduction

Python 3.10+ and SymPy are sufficient for the exact dossier checks. Run in a temporary copy to preserve the archived manifest, since the scripts rewrite their output JSON:

```sh
cp -R references/holden-mi16-2026-09-12/dossier /tmp/mi16-rerun
cd /tmp/mi16-rerun
python3 code/verify.py
python3 code/verify_selector.py
python3 input_findings_MI16/verify_exact.py
```

The independent reviewer reran 12,832 supplied checks and seven selector cases, including the exact order-two moment at p=1296, and wrote 8,175 independent rational checks. New results are saved as `rerun-exact_checks.json`, `rerun-selector_checks.json`, and [reviewer-check.py](reviewer-check.py); the [report](independent-review.md) describes their scope. Finite tests support the analytic proof and are not universal certificates. No nontrivial general order-three elimination or high-order general implementation success is claimed.

Build the authored solution with three passes of `pdflatex` on `matrix-inequalities-and-norms/MI-16/solution.tex`. Repository validation and visual inspection are recorded in [publication-checks.md](publication-checks.md).
