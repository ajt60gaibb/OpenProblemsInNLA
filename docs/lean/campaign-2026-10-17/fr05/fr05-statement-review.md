# FR-05 independent statement and provenance review

Reviewed 17 October 2026 by `/root/fr05_statement`. This is a source and statement review, not a fresh Lean build, kernel replay, or complete rederivation of every analytic estimate.

**Verdict:** The preserved FR-05 target is the vanishing limit, and the newer manuscript and existing upstream Lean exports state that target exactly. The current working branch is stale: its `Open` page is not evidence that FR-05 still lacks a proof. At the locally available published base `47006df8b3a6c724a557266c891893d03e69323a`, FR-05 is already `Lean verified`, with the full proof and a recorded Linux Comparator/LeanCert kernel receipt. Validate that evidence before undertaking a duplicate proof.

## Original and exact obligations

The permanent registry maps `FR-05` to `frames-and-matrix-designs/FR-05/README.md`. The working README and generated TeX agree on the following statement:

1. For every natural dimension `d ≥ 2`, the frame has exactly `4d − 5` rows and `d` complex columns.
2. All real and imaginary matrix coordinates are independent `N(0,1/2)`. The law is the standard complex Gaussian, rather than a real Gaussian or an arbitrary isotropic law.
3. An injective frame satisfies, **for every** pair `x,y ∈ ℂᵈ`, equality of all componentwise moduli `|Ax| = |Ay|` only when `y = exp(iθ)x` for some real `θ`. Zero signals are included. An almost-every-signal conclusion is insufficient.
4. `p_d` is the probability of that frame event, and the required conclusion is `p_d → 0` as `d → ∞`.

The original page explicitly excludes the earlier result `p_d < 1`. That inequality alone gives no convergence to zero. The primary [Randomstrasse statement, Conjecture 19](https://arxiv.org/html/2603.29571v1) separately states the strict inequality and the limit. Li's [June 2026 arXiv paper](https://arxiv.org/abs/2606.17922) announces positive noninjectivity probability and part (1) only.

## Newer source, independently checked

The archived source at immutable revision `bca7904b8d6f43b7258bc0eaed636a2b6b4a8792` is the 13-page manuscript [*Resolution of Vinzant's Conjecture on Phase Retrieval Injectivity*](https://zhangsong-li.github.io/injectivity_phase_retrieval.pdf), dated 13 September 2026. I extracted the PDF directly from Git and checked its SHA-256:

`d1be40e71e492fc16aed05ca8e71153a8e2114a2af8218a7700a4ec3c6897254`.

Printed page 1 defines the same all-signals phase quotient, the same row count, dimensions `M ≥ 2`, and independent real/imaginary `N(0,1/2)` coordinates. Printed page 2, Theorem 1.4, asserts one constant `C > 0` such that `p_M ≤ C/M` for every `M ≥ 2`, and then the limit. This quantitative strengthening therefore implies FR-05 without replacing its original target. The earlier June arXiv abstract is not the provenance of this stronger theorem.

The web reader could access the earlier arXiv sources but could not retrieve the newer manuscript URL during this review. The September claim above is based on the hash-bound archived primary manuscript, not an inference from the June abstract. Its repository copy is [available at the reviewed revision](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/bca7904b8d6f43b7258bc0eaed636a2b6b4a8792/frames-and-matrix-designs/FR-05/lean/sources/injectivity_phase_retrieval.pdf).

## Existing Lean boundary

I inspected the following source files at that same immutable proof revision:

| Obligation | Source inspected | Finding |
| --- | --- | --- |
| Actual complex measurement matrix and all-signals modulus event | `NLA/FR05/Definitions.lean` | `Frame m d = Matrix (Fin m) (Fin d) ℂ`; the row is the complex sum `∑ j, A i j * x j`; `PhaseRetrievalInjective` universally quantifies both signals. |
| Global phase | `NLA/FR05/Definitions.lean` | Witness `θ : ℝ` and `y = Complex.exp (θ * Complex.I) • x`, matching the original page. |
| Exact Gaussian probability | `NLA/FR05/Probability.lean` | Standard Gaussian on every finite real matrix coordinate, mapped to real/imaginary entries and scaled by `(sqrt 2)⁻¹`; event probability taken at `4 * d - 5` rows. |
| Genuine measurable event | `NLA/FR05/Geometry/InjectivityMeasurable.lean` | Proves `MeasurableSet {A | PhaseRetrievalInjective A}` for every finite frame size, rather than leaving outer probability as the final interpretation. |
| Unconditional quantitative conclusion | `Solution.lean` and `NLA/FR05/FinalAssembly.lean` | `∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d → phaseRetrievalProbability d ≤ C / d`. No likelihood estimate, Newton success event, or analytic inequality remains as a hypothesis of the export. |
| Original limit | Same files | `Filter.Tendsto phaseRetrievalProbability Filter.atTop (𝓝 0)`. The finitely many values at dimensions 0 and 1 are irrelevant to this limit; the quantitative theorem restricts to `d ≥ 2`. |

The final assembly proves the source-specific comparison, applies the inverse-dimension reduction, and squeezes the nonnegative probability by `C/d`. This statement review does not independently reprove the 112-module import closure.

The [existing proof source](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/bca7904b8d6f43b7258bc0eaed636a2b6b4a8792/frames-and-matrix-designs/FR-05/lean/Solution.lean) exports both main conclusions. `Challenge.lean` has four intentional statement placeholders; `Solution.lean` imports `NLA.FR05.Proof`, not `Challenge`. The Comparator configuration selects the quantitative theorem, limit, an explicit noninjective frame, and the second-moment algebraic reduction, permitting only `propext`, `Classical.choice`, and `Quot.sound`. A proof of the explicit frame alone would not settle the probability problem.

## Published evidence and remaining campaign check

The existing [independent review](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/bca7904b8d6f43b7258bc0eaed636a2b6b4a8792/docs/lean/proofs/FR-05/INDEPENDENT_REVIEW.md) and [Linux CI receipt](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/bca7904b8d6f43b7258bc0eaed636a2b6b4a8792/docs/lean/proofs/FR-05/LINUX_CI_RECEIPT.md) record a successful [9 October job](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/38000947893/job/114058782811): isolated Comparator acceptance plus LeanCert `#assert_trust kernel` for all four selected exports. The receipt identifies source merge commit `e70f6976c51d4ef1246b395aeb0ff0678b9483e1`, PR head `1d262c8609a6ba3cfd85989fa8ac1317a04fec93`, and hashes of the result and logs. These are existing claims inspected from Git; I did not download or replay the artifact in this subtask. The web reader also could not fetch that Actions URL, so this review does not independently certify its current accessibility.

The next evidence task is to obtain and verify the artifact, compare its source snapshot to the reused proof, and reproduce the pinned harness as requested. Preserve both originals and the immutable proof reference while doing so. The historical `formalization.yaml` and Challenge commentary still say independent review or isolated verification is pending; these descriptions predate the later review and receipt and should be identified as historical metadata if reused.

The companion [input hash record](fr05-statement-review-inputs.json) binds the working originals, registry mapping, reviewed proof revision, and exact Lean sources. This subtask added only review files; it changed no canonical problem page, ID, mathematical target, status, TeX, PDF, or existing proof.
