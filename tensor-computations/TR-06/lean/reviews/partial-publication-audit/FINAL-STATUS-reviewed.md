# TR-06 partial Lean formalization — INCOMPLETE

Current state: 26 September 2026. This is an explicitly incomplete development
snapshot for a draft pull request. The full finite-mean angular-condition-number
theorem is not formally verified. The canonical problem retains **Solved** status.

George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, with substantial AI assistance.
The original mathematical proof remains attributed to Matthew J. Colbrook.
Contribution reviews were performed by independent AI agents; no external human
peer review or source-author endorsement is claimed.

Two independent agents approved the complete ten-declaration statement boundary
in [statement-freeze.json](reviews/statement-freeze.json). The frozen README and
earlier review snapshots retain historical pre-implementation wording. This file
records subsequent progress without changing the approved source bytes.

| Exact Challenge declaration | Current implementation status |
| --- | --- |
| `derivativeRatio_eq_operatorNorm` | Independently reviewed local proof |
| `angularSlope_eq_chart_derivative` | Independently reviewed local proof |
| `induced_volume_chart` | Independently reviewed local proof |
| `regular_locus` | Incomplete |
| `finite_angular_mean` | Incomplete |
| `generic_iff_source` | Independently reviewed local proof |
| `smooth_locus_correspondence` | Incomplete |
| `smooth_chart_is_local_addition_inverse` | Independently reviewed local proof |
| `source_model_correspondence` | Incomplete |
| `finite_angular_mean_source` | Incomplete |

Names are in namespace `NLA.TR06`. Implementations of the five correspondence
statements are in separate supporting modules; `Challenge.lean` remains a frozen
specification with ten intentional placeholders. There is no `Solution.lean`.
Five correspondence proofs do not represent half of the mathematical work:
the principal regularity and integrability obligations remain open.

The 57 supporting implementation, definition and audit modules include exact
radial Gaussian convergence, positive radial homogeneity, sampling-locus and
chart-locus measurability, weighted area, source-dimensional null-image transfer,
L2 graph Jacobian inequalities, a uniform coordinate-projection atlas, and
finite-volume estimates conditional on explicit bounded-overlap hypotheses.
Polynomial real-zero-locus nullity is proved in coordinate-space Lebesgue measure;
its transfer to the actual exceptional tensor locus is still missing.

Algebraic results now identify the complete closed rank-one cone and its character
algebra, construct exact-dimensional Segre coordinates, prove finite complete
fibers at identifiable exact-rank tensors, derive exact rank from finite nonempty
complete fibers under the stated format restrictions, and prove generic finite
localization of the actual addition algebra. Generic unramified localization and
uniform character bounds are also proved. Conditional analytic results construct
actual smooth decomposition charts from relative properness, identifiability and
injectivity of the derivative. Their premises still need to be established from
the original generic complex identifiability assumption.

Remaining obligations include the full-measure regular locus and smooth-locus
correspondence, the actual normalized graph's bounded volume, the induced-volume
polar formula, positive finite normalization, source-model correspondence, and
the complete finite-mean theorem. The abstract algebraic and graph estimates do
not by themselves discharge these obligations.

The combined local build of frozen Definitions plus all 57 supporting/audit
modules passed with Lean 4.33.1 and pinned Mathlib/LeanCert sources. Audited proof
closures use only `propext`, `Classical.choice` and `Quot.sound`; LeanCert
`#assert_trust kernel` checks pass. The build reused prebuilt dependency artifacts.
[Combined build receipts](reviews/partial-release-evidence/development-proof-check.json)
and independent contribution reviews are retained in `reviews/`. No numerical
quadrature or approximated constant is used.

This is **not** an authoritative fresh Linux build, a full-target Lean4 Comparator
run, or an independent kernel replay. Metadata reports `main_results: []`,
`completed_target_count: 0`, `complete_problem_verified: false`, and verification
steps not run. The v0.4 schema passes; the strict completed-project manifest gate
intentionally rejects this incomplete project. The existing full-verification CI
job is therefore expected to fail. It has not been weakened or bypassed.

For development checking, run `python3 development_proofs.py --help` from this
directory and supply the pinned Lean executable, package and LeanCert cache paths,
an external build directory and an evidence directory. The retained receipt
records the exact local command and dependency revisions. Plain `lake build`
still targets the future Solution and is not a working complete-project check.
The eventual authoritative acceptance command is `tools/lean/verify.sh` from the
repository root, once all complete-target obligations and metadata are fulfilled.

The shared infrastructure and permanent-ID checks passed. Canonical README,
original statement/TeX/PDF, original proof manuscript, permanent registry,
catalogs and prior verifications remain unchanged. This draft must not be
presented or merged as a completed TR-06 verification.
