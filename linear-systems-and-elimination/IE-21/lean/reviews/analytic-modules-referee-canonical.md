# IE-21 independent review of six analytic modules

**Verdict: APPROVE, module by module, at the exact hashes below.** No mathematical correspondence defect or prohibited proof dependency was found. This is a bounded proof-module review, not a full IE-21 verification.

Reviewer: Codex subagent `/root/canonical_inventory`, a nonauthor of all six reviewed proof modules. I authored the frozen statement draft and the separate MatrixSemantics/FiniteTrimming modules; I therefore do **not** qualify as an independent final whole-problem referee. I made no changes to any reviewed proof source, frozen boundary, canonical page, status, or Solution.

| Reviewed proof module | Verdict | SHA-256 |
|---|---|---|
| `NLA/IE21/GaussianTrimming.lean` | APPROVE | `e01148c5f0dc4d08b829bd61db1e0b4061ad7a24968320813068211e6ec6ec55` |
| `NLA/IE21/PopulationTrimming.lean` | APPROVE | `fce653d1b4b34543e45f9cdf8f450350c0c8efd677964bb030732b5b0731ed85` |
| `NLA/IE21/SphericalLaw.lean` | APPROVE | `d0615cad430beccf40425c539b26f6bca97669783574f502bf5a17c26e888f62` |
| `NLA/IE21/RowLaw.lean` | APPROVE | `4e74a756467094b97beddb27e401a4cb93fb7d546d2293a53133d8fe32580995` |
| `NLA/IE21/GaussianPolar.lean` | APPROVE | `e8da1ca7e2ae4d1285cf798d0b64c8da2a2cec5982008c9153cbe60426a32f3f` |
| `NLA/IE21/AspectSchedule.lean` | APPROVE | `55b52dee2d864d2053325e9d10c4e834ef688d0cb32a59f030fc064ff22cb111` |

## Mathematical and correspondence checks

**GaussianTrimming — APPROVE.** The central absolute-Gaussian mass is proved continuous, strictly increasing on nonnegative radii, zero at zero, and tending to one. The intermediate-value argument produces the positive θ-quantile. The literal `sInf` definition of `gaussianCutoff` is proved to equal this quantile through its least-element property; it is not used through a default value. The density computation identifies the exact canonical integral with the actual truncated second moment. Integrability and the standard-Gaussian second moment justify the bound between zero and one. `gaussian_constant` matches the entire frozen statement, with only `0<θ<1` as its numerical premise.

**PopulationTrimming — APPROVE (helper scope).** The admissible threshold objective set is explicitly nonempty and bounded above under the stated first-moment and probability assumptions. Thus the real supremum has the intended optimization semantics. Law transport follows from actual pushforward integration. The coupling inequality follows from the 1-Lipschitz hinge function and both supremum comparisons, rather than an assumed selector or quantile theorem. The quantile-attainment lemma explicitly requires an exact lower-tail mass and a nonnegative cutoff; it does not claim such a cutoff exists for arbitrary atomic laws. Its standard-Gaussian specialization proves equality with the already verified canonical integral. These helpers alone do not prove spherical trimming or concentration.

**SphericalLaw — APPROVE.** The probability law is literally normalized `volume.toSphere`, with positivity and finiteness of the normalization mass proved for `n≥1`. Pushing the sphere subtype into Euclidean space proves unit-norm support. The extra Gaussian projection lemma uses the genuine `stdGaussian` law and its covariance, with a unit projection vector. No Gaussian representation is smuggled into the surface-law definition.

**RowLaw — APPROVE.** Matrix-row and row-matrix maps are measurable exact inverses. The canonical matrix law is the actual finite independent product pushforward. Its marginals, independence and unit-row support are proved, including the vacuous zero-row case. `independent_row_transport` applies to arbitrary probability spaces and measurable matrices satisfying the explicitly stated independent surface-law row hypothesis; no row-rank, aspect-ratio, or common-space assumption is added.

**GaussianPolar — APPROVE (completed polar-law components only).** The product Gaussian density is transported through the Euclidean coordinate isometry with the correct factor `(sqrt(2*pi))^(-n) exp(-r^2/2)`. Mathlib's actual polar-coordinate measure theorem gives raw surface measure times the radial density against `r^(n-1) dr`. Positive finite surface mass then normalizes the two factors. Removing the origin is justified by Gaussian absolute continuity and its zero mass when `n≥1`; no nonzero-input hypothesis is imposed on the random draw. Pushforward of the normalized polar product proves the direction law, norm law, and radius-direction independence. Radius moments and the complete frozen `gaussian_surface_correspondence` theorem are **not** approved here: the active GaussianMoments module was deliberately excluded.

**AspectSchedule — APPROVE.** The schedule is exactly `d=32 sqrt(log(Q)/Q)`, where `Q=m/n`. For eventual `Q≥9`, `log(Q)≥1`, and `d≤1`, the proof establishes the net base bound `1+2/d≤Q`. The identity `m*d^2=1024*n*log(Q)` yields the exact first and second tail exponents `-2*n*log(Q)` and `-2048*n*log(Q)`. Both tails are bounded by their coefficient times `1/Q`, giving the explicit total `F≤7/Q`. This proves failure decay for every diverging aspect ratio, without any growth-rate restriction involving n. Separately, `n→∞` and `Q→∞` imply `m→∞`, all error numerator terms tend to zero, and `1-d→1`; the ratio error therefore tends to zero. Eventual strict parameter positivity/ranges and `n≥2` are included in the result. `aspect_schedule` matches the complete frozen signature.

## Independent build and axiom evidence

I rebuilt the frozen Definitions and all six reviewed modules into a newly created external directory, then compiled a separate exact-signature check and a public-declaration axiom audit. The build used the campaign's pinned Lean 4.33.1 and package cache, never any author's local proof oleans. No Challenge import was used. All nine compilation steps passed with zero errors and zero warnings.

The five complete selected signatures checked independently are `surface_probability`, `gaussian_constant`, `product_row_semantics`, `independent_row_transport`, and `aspect_schedule`. A separate application checked the three completed polar-law conclusions against their literal frozen meanings. This was not an actual Lean4 Comparator execution; that gate remains required for the final Solution.

All 50 public declarations in the six modules have transitive axiom closure contained in—and here equal to—`propext`, `Classical.choice`, `Quot.sound`. Private lemmas used by them are included transitively. No reviewed source imports Challenge or uses custom axioms, sorry/admit, native_decide, or run_tac. All four frozen mathematical/configuration hashes match `statement-freeze.json` before and after the review.

Fresh build directory: `/private/tmp/nla-ie21-analytic-independent-1zb7brvh`.

Exact independent log SHA-256: `894ceb3c03e20ccb6b3036ff2349a7cd3aa08ae1544fb633d97e5e7c863f2e8a`.

Exact machine-readable receipt: `analytic-referee-canonical-evidence/review-receipt.json`; reproduction script, source input receipt, build receipt, signature checker, axiom checker and raw log are adjacent. No complete-problem, final LeanCert, Comparator, or canonical status approval is implied.
