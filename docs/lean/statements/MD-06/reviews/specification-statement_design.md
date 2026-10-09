# MD-06: independent specification review

Reviewer: /root/statement_design (OpenAI Codex AI agent), 2026-09-28.
Verdict: **approve** for the bound specification bytes.

## Fidelity reasoning

1. Target retains the original limit-one conjecture exactly, despite its negative resolution. NegativeResolution is a separate limit-zero proposition, and QuantitativeResolution a separately credited stability strengthening. The contradictory limits are not conjoined or silently substituted for the historical question.

2. The finite ratio counts all labelled simple cubic graphs on Fin n, not isomorphism classes, connected graphs or configuration-model multigraphs. The denominator is nonzero at every even n>=4, and 2*(k+2) enumerates precisely those sizes. Thus the proposed ordinary real sequence limit is the original even-subsequence limit.

3. Fin n -> Real.Angle supplies the actual full product torus. Synchronization is equality of every pair modulo 2*pi, including across components. IsLocalMin uses the ordinary non-strict topological local minimum of the whole torus; no rotation quotient, stationary-point surrogate or strict-minimum requirement changes the original event.

4. The energy and Hessian sum each unordered edge once by i<j. The gradient sum includes every neighbor with sin(theta_i-theta_j), matching direct differentiation. Hessian directions are ordinary real vectors, and mean zero and norm square are the literal finite sums, not angle-valued directions.

5. The retained manuscript was read through its deterministic and probabilistic arguments. Its c0>1/16 and gamma=1/10 imply edge cosine at least c0/2>1/32 and Hessian at least c0/20>1/320 on mean-zero directions. The proposed strict edge bound faithfully preserves the old stronger resolution; explicit local minimality is justified by the same manuscript and kept in the event.

6. QuantitativeResolution existentially chooses a nonsynchronized critical local minimum for each graph, requires all four displayed conditions together, and tends to probability one with no finite-n rate or phase initialization law. Every constant and direction quantifier remains independent of graph size.

7. The auxiliary certificate threshold, correction radius, F_R root profile, c0, clean fixed-radius neighborhood, 2^(R-1) bound and R=29+ceil(log2 ell) agree with the source. The order fixing ell,R before n and only subsequently taking ell large is preserved; no independent-event or uniform-growing-neighborhood assertion is added.

8. The old abstract ScalarModel/Semantics and its resolution-only CompleteTarget were inspected. The proposed concrete graph, topology, probability and limit definitions fix their actual missing semantics without claiming the older projection lemmas prove the problem.

## Bound inputs

- docs/lean/statements/MD-06/NUMERICAL_TARGETS.md: 4c5298cda03585cf6c596373e94efe5605ea7f8511714f6b6373f03035a2e02f
- docs/lean/statements/MD-06/ORIGINAL.md: b51eaf3dd9c4f4a806ca01125997909a625af86477d3daad5a7e095746c3f039
- docs/lean/statements/MD-06/source-lock.json: 0a8fa957a1077a04332633ae7d510f07b3f57ab1b31763e30142b02dab879278
- matrix-discrepancy-and-optimization/MD-06/README.md: b51eaf3dd9c4f4a806ca01125997909a625af86477d3daad5a7e095746c3f039
- matrix-discrepancy-and-optimization/MD-06/lean/Challenge.lean: afbbc0c0a7b8992c3a1f46957fb4ad48622715232ec4703fd79460f70248d46d
- matrix-discrepancy-and-optimization/MD-06/lean/Definitions.lean: 825abcba56f43f21360449983a4d8690fd1cdd70bf756bcdb29e92fd6bbcf4f8
- matrix-discrepancy-and-optimization/MD-06/lean/FIDELITY-BLOCKER.md: 19b64b81da95b6badd053e9cfc4a21ebe3651935609d04eacd1c56e1ecfd4494
- matrix-discrepancy-and-optimization/MD-06/lean/SPEC.md: 98eab619fed7b0ca38be6033cd3526c480ecc2781e8acda25f32eeb80dec8f98
- matrix-discrepancy-and-optimization/MD-06/lean/Solution.lean: 252f4e19d29a27ce744610f7ce4886f4a4646f2fbb426073deb479e5cc10043f
- matrix-discrepancy-and-optimization/MD-06/problem.tex: 9efb994b165f17d0d65a91df729dcb0ab6e5afc144d7b10c8ec1fde11abdb1ce
- references/colbrook-discrepancy-2026-09-11/manuscripts/MD-06.tex: 3804a3121d5733665bde98008a8f5226b4d30afe945aec3d712f2de07b9200b9

## Limits

Independent AI-agent preimplementation specification review. Reviewer /root/statement_design did not author this specification. The full canonical page and cited archived source were inspected and source locks checked; this report approves mathematical/model correspondence only. No new Lean implementation, target proof, executable solver, or numerical certificate is approved. Final source/import/pin and actual kernel/frozen-identity reviews remain required.
