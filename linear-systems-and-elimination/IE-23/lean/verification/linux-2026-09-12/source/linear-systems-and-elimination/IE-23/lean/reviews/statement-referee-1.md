# IE-23 independent statement referee 1

**APPROVE the frozen mathematical boundary and the additive Comparator configuration.** No mathematical correction is required. This is statement review, not proof verification or approval of a Linux execution.

Reviewer: OpenAI Codex AI agent `/root/solved_statement_inventory`, independent of author `/root/leancert_examples`. Date: 12 September 2026. I did not author or edit the definitions, Challenge, numerical targets, configuration or proposed proof. I independently read the complete canonical README, complete standalone Colbrook manuscript, complete informal review and submission record, then the actual Lean definitions and all eight Challenge contracts. PDF identities were checked against Git; visual PDF review is not claimed by this statement audit.

## Frozen scope and resolved configuration omission

The original freeze `6e9b62ab46974a54204ba7636ec83209bd102fd322794709c83a46df85d417f1` binds 32 project files and eight original source files at upstream `f41f1f9ffa2171550d4bb795862c6170c4f26070`. Its historical handoff remains unchanged. This approval additionally binds:

- `comparator.json`: `8a02cee6a555e2bd658cb2daa22bfaba515027d787d570846aae21aaac2e26cb`.
- `reviews/statement-config-supplement.json`: `dafd6645aa017c543dd4eb9f60633b47a2035f090d58955525a3d6c41156141a`.
- `reviews/statement-config-supplement.md`: `95c93d583cf9a29c7588052c6f29e4080cd642f33709c7d25649cf026194b8ec`.

Root's missing-configuration finding is resolved by that expressly authorized additive configuration. I parsed it independently: it selects exactly all eight frozen Challenge names, uses the proper Challenge/Solution modules, has no definition exceptions, and allows exactly the standard three axioms. The original default remains Challenge and Solution was registered initially. No Lean or dependency input changed, so no new mathematical statement or fresh elaboration was needed for this JSON-only addition.

The central mathematical hashes are:

| File | SHA-256 |
| --- | --- |
| `NLA/IE23/Definitions.lean` | `1af986f21059b5b9862decf09366d3ea8dba0c965a5b8550b8d9a0fcc41af33f` |
| `Challenge.lean` | `faf9ae407be25d4fded2737a4dd4ef41a329a3cc25e194c0d06159b6a788319d` |
| `NUMERICAL_TARGETS.md` | `eb49c0b56617ab749184cef753d22ec461eef982a68d46b352187d1843b60d28` |

Every original project hash matched before and after my checks. All eight original sources matched both current worktree bytes and exact base Git blobs. No proof module or Solution exists at this review's final identity check.

## Fidelity, nonvacuity and full quantifiers

`RightInverseUniqueConjecture` preserves all complex matrices, all `1 ≤ m < n`, actual rank m, every finite real p greater than two, and every distinct complex right inverse. Its objective is the direct induced norm of X, not that of XA. The canonical full-row-rank Moore–Penrose formula is represented by actual conjugate transpose and Mathlib matrix inverse; no proposed inverse is installed as its meaning. The finite-real-p quantifier correctly excludes p=2 and p=infinity.

Actual elaboration identifies the numerator as `PiLp.instNorm` at exponent two on `EuclideanSpace ℂ`, not the supremum norm on plain functions. The denominator uses `Complex.instNorm`, a finite sum over every input coordinate, and `Real.rpow` for both real exponents p and 1/p. The ratio set includes every nonzero complex vector. Its supremum is the actual `Real.instSupSet`; it is not an abstract norm field or a prescribed witness value.

The first contract proves positive denominator, nonempty and bounded ratio set, the real least-upper-bound property, nonnegativity and the all-vector norm bound for every original input domain. Those facts are conclusions, so an empty or unbounded conditional supremum cannot manufacture this counterexample. Its harmless extension to output dimension zero also remains mathematically valid. Positivity follows from a nonzero coordinate; boundedness can follow from each coordinate being bounded by the p-norm and the sum of Euclidean column norms. No unformalized all-p Schatten or matrix spectral foundation is needed.

Rank is the actual complex finrank of the matrix linear range. The witness contract proves full row rank, a genuine unit Gram matrix, its actual inverse, the Moore–Penrose identity and both right-inverse equations. Thus no totalized-inverse default is used. The generic full-row-rank formula need not be assumed correct through an extra premise: it is the original definition and is explicitly verified at the counterexample.

The final contract negates the **entire original universal conjecture**. Choosing the admitted value p=4, with m=2 and n=3, is sufficient for that negative answer; the universal statement itself is not restricted to p=4. The eight exports additionally prove both inverses are global minimizers and that the minimum is attained. `IsNormMinimizer` quantifies every complex competing right inverse, and the competitor action identity is a theorem conclusion for arbitrary such Y. It is not an assumed guessed parameterization.

## Independent exact mathematical diagnosis

I independently checked eight rational matrix identities, including both products for the proposed Gram inverse, actual A times B and X, and both Gram products. The last two columns of A give a determinant-one minor. The norming vector z=(1,-1) is nonzero and Bz=Xz=(0,1,-1), with squared Euclidean norm two and fourth-power denominator two.

My separate standard-library polynomial diagnostic uses arbitrary real and imaginary coordinates, rather than numerical complex samples. It confirms

\[
\|By\|_2^2+|y_0+y_1|^2/3=\|y\|_2^2,
\qquad \|Xy\|_2^2=\|y\|_2^2.
\]

The fourth-power comparison reduces exactly to the nonnegative square of the difference of the two squared coordinate moduli. Every right inverse satisfies the linear row constraints giving Yz=(t,1-t,-1-t), for arbitrary complex t. The coefficientwise identity is then `‖Yz‖₂² = 2 + 3|t|²`. This supplies the correct global-minimality lower bound. Positivity and real-power monotonicity still have to connect these exact identities to the actual roots, unsquared norms and suprema; the contracts expressly require those bridges.

The proposed constant is the actual positive fourth root of two, `sqrt (sqrt 2)`, and its equivalence with the source expression `2^(1/2-1/4)` is a conclusion. Zero input vectors, complex phases, strict p and dimension endpoints, and the nonzero norming denominator are all covered without additional assumptions.

## Fresh checks, library reuse and trust

I freshly compiled Definitions and Challenge into a separate prefix, followed by my own semantic inspector. All three commands passed; Challenge produced exactly eight intentional placeholder warnings. The inspector printed all eight signatures and the actual norm, real-power, matrix-rank, matrix-inverse and supremum instances. It ran 17 core-definition `#print axioms` and explicit `#assert_trust kernel` checks; all reported axioms are subsets of `propext`, `Classical.choice` and `Quot.sound`. This audit does not claim those Challenge placeholders are proved.

The ten dependency source checkouts match the manifest and have clean Git status. I reused available dependency objects read-only from MI-22, excluding all prior project objects and using a new IE-23 referee prefix. The unused Cli checkout has no built-object directory. Lean is 4.33.1; Mathlib is `0df444a360eaa60ab8c11dca51a86af692955474`; LeanCert is `621a43d7cf21f87872392a01e874f2f1dbddc926`. This is local macOS checking, not a full dependency-source rebuild or Linux Comparator run.

I inspected the pinned `EuclideanSpace`/norm-square definitions, `Matrix.rank`, the nonsingular inverse definition and its unit hypotheses, real-power APIs, and conditional-supremum rules. These genuine existing APIs support the intended proof route. The compact definitions, source separation, descriptive names, and source-mapping documentation are appropriate. No custom axiom, native proof, unsafe evaluator, replaceable definition hole or conclusion hidden in a hypothesis was introduced by this boundary.

Pure exact algebra and analytic norm properties suffice here. I approve the disclosed LeanCert **kernel trust audit** scope without an artificial interval certificate. A final proof must still consume genuine mathematical bridges and pass the separate runtime kernel/Comparator gates. This applies the relevant Tau Ceti-derived scope, correctness, reuse, generality, API, documentation and attribution checks from `docs/lean/REVIEW.md`; no official Tau Ceti endorsement is implied.

Mathematical authorship remains Matthew J. Colbrook's, with the original small matrix attributed to Dokmanić and Gribonval. George Stepaniants is credited for formalization with the complete Caltech Department of Computing and Mathematical Sciences affiliation and no new contact email. The source's stronger all-p norm formulas, complete minimizer disk/ball, endpoint results and smallest-dimension classification are explicitly outside the advertised formal exports. That scope distinction is truthful and does not reduce the complete negative canonical answer.

Raw commands and hashes are in `statement-referee-1-evidence/`. The fresh-check receipt is `99df183b0e09b684cc7083d40c5d74c5bb7ca205ef31e304128e3df0c0ba054b`; the actual semantic-inspection log is `91e764a2b7aab50aa3b78e7611085dbc7cea62d8b4f16b3eefb6b5a601568525`. The evidence manifest binds the reproducible scripts, exact diagnostics, before/after identities and this report.

**Remaining gates:** the second independent statement approval, complete proof, two independent final proof reviews, actual Linux verification with controls, and independent operational review. This approval alone does not change canonical status or authorize publication.
