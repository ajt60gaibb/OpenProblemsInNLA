# MF-24: polynomial norm ratios for super-identical pseudospectra

This project implements the complete negative answer to MF-24: no constant
uniformly compares the polynomial operator norms of all matrix pairs with
super-identical pseudospectra. The original mathematical counterexample is by
**Georg Maierhofer, University of Cambridge**. The formalization is by
**George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology**, with substantial OpenAI Codex assistance.

**The complete 22-target proof passed canonical Linux verification.**
[Run 35033148310](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35033148310/job/104596164346)
checked immutable proof commit `208e30d80f73ef661b1f019c7de93c70254f7e48`
on 15 September 2026. LeanCert kernel assertions, actual non-root Comparator,
default-kernel replay, standard transitive axioms and all required rejection
and sandbox controls passed. The [original logs and hashes](verification/linux-2026-09-15)
and both [independent final referee reports](reviews/final) are retained.
Later documentation commits are distinct from that exact checked revision and
require their own published-commit execution for the campaign record.

The earlier combined development run 35031607095 passed the complete MF-24
component but failed in MF-12. Its original status and evidence are preserved;
it is not relabeled as a successful aggregate run.

The definitions use actual complex polynomial evaluation, the induced norm on
complex Euclidean space and every ordered singular value after every complex
shift, including multiplicities and zeros. For each integer $`m\ge2`$, the
source family has dimension $`(m+1)^2`$. Its explicit polynomial satisfies

```math
\|p_m(X_m(t))\|_2\ge t^2\sqrt m,
\qquad 0<\|p_m(Y_m(t))\|_2\le t^2+m \quad(t>1).
```

At $`t=m`$ the ratio is at least $`(2/3)\sqrt m`$. The final theorem supplies
an actual finite witness beyond every proposed real bound and contradicts the
entire original uniform comparison. The conservative denominator estimate
keeps every residue-class coordinate. Sharper constants and additional
dimension-padding corollaries of the manuscript are outside this formalization.

The proof uses sparse path identities, genuine Gram determinants and a generic
two-dimensional transfer identity to prove full singular-value equality. Exact
finite sums and Cauchy–Schwarz give the norm estimates. Only fixed small
identities are expanded; growing matrices are handled symbolically. LeanCert
checks all exported results in kernel mode. No numerical singular-value search
or artificial interval calculation is used.

[Definitions](NLA/MF24/Definitions.lean), the independent
[Challenge](Challenge.lean), [numerical obligations](NUMERICAL_TARGETS.md) and
[statement freeze](STATEMENT-FREEZE.json) record the approved boundary from
before implementation. [Solution](Solution.lean) imports the complete proof
without importing Challenge; [Unbounded](NLA/MF24/Unbounded.lean) proves
`NLA.MF24.arbitrarily_large_ratios` and `NLA.MF24.no_uniform_comparison`.
[SourceCorrespondence.md](SourceCorrespondence.md) contains the full 22-result
map. Its introductory draft-stage wording is retained as part of the immutable
pre-proof record; this README and [formalization.yaml](formalization.yaml)
describe the completed canonical verification. Every result is selected by
[comparator.json](comparator.json), with no replaceable definitions and only
`propext`, `Classical.choice` and `Quot.sound` allowed.

From this directory, a routine Lean check is:

```bash
lake exe cache get && lake build
```

The default target is the complete Solution. The recorded
[tooling transition](PUBLICATION-TRANSITION.json) changes only that default from
the earlier statement-stage Challenge and preserves its original snapshot.
For the complete isolated Linux check, use the repository's
[shared checker instructions](../../../docs/lean/README.md) and
`tools/lean/verify.sh matrix-functions-and-stability/MF-24/lean /tmp/nla-lean-tools`
after preparing the pinned checker and Linux isolation. CI performs that
preparation and runs the same check.

The [root mathematical review](reviews/root-source/REVIEW.md),
[current-byte acceptance](reviews/root-source/DEVELOPMENT-ACCEPTANCE.md) and
[independent mathematical review](reviews/independent-source/REVIEW.md) apply
the repository's scoped Tau Ceti protocol. Both mathematical referees
contributed no proof code. Historical statement approvals and snapshots remain
under `statement-audit/`; development evidence is under
`verification/development-35031607095/`. These are AI-agent reviews and audits
of actual executions, not external human peer review or official endorsement.
The pinned Schiffer and Forsythe references, Mathlib APIs, source attribution,
automation and current limits are recorded in the manifest.
