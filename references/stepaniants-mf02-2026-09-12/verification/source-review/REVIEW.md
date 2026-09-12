# MF-02: independent source, prior-art, and exact-scope review

Reviewer: independent AI agent `/root/review_md03_md04`.

Review date: 12 September 2026 (UTC). This is an agent review, not human peer review, formal verification, or a guarantee of novelty. The reviewer did not author the candidate under review. A separate agent is responsible for the adversarial mathematical audit.

## Bound sources and verdict

Candidate: `../RESULT.md`, 11,177 bytes, SHA-256 `63d6a0dccebaf43b7da3dc6b2615755c3c3d24791a12527007f1276256e89ba9`.

Canonical target: `canonical-statement.md`, 2,393 bytes, SHA-256 `1312362ce7bbe162adba3b9305acd2f8cd31dd7d8c8d056ce0138c0b25243127`.

**Scope verdict: the candidate's uniform two-sided order answers the literal canonical request for asymptotic dependence on both parameters. Recommend a carefully attributed canonical resolution/status-correction submission, conditional on the separate full mathematical PASS. Do not describe the original source's exact smallest-stage problem or same-budget error comparison as fully solved.**

The correct priority distinction has three parts:

1. I did not find an inspected publication explicitly stating the canonical quantity and the uniform theorem for `T_min(m,delta)`.
2. A uniform constant-factor order already follows by a short synthesis of published general estimates and a classical degree lower bound. The synthesis is written below. This is not a claim that the earlier paper printed that precise corollary, nor that this corollary is novel.
3. The candidate provides the stronger explicit upper guarantee `T_min(m,delta) <= m` for `m >= 1`, together with its lower bound and two endpoint values. Its iteration is already known. I did not find its particular global comparison or this explicit upper guarantee in the inspected sources; that limited search finding is not a priority claim.

## What is already in the literature

### Cheon, Kim, and Kim (2020)

Jung Hee Cheon, Dongwoo Kim, and Duhyeong Kim, *Efficient Homomorphic Comparison Methods with Optimal Complexity*, ASIACRYPT 2020, pp. 221-256, DOI [10.1007/978-3-030-64834-3_8](https://doi.org/10.1007/978-3-030-64834-3_8); [primary ePrint record](https://eprint.iacr.org/2019/1234), [primary PDF](https://eprint.iacr.org/2019/1234.pdf).

The relevant locators use the PDF's printed page numbers: Section 2.1, p. 9 (only nonscalar multiplications counted); Lemma 3, p. 14 (a global one-step inequality); Theorem 3, p. 15 (composition convergence); Table 1, p. 17 (the cubic case costs two products per stage); Section 3.4, pp. 17-18 (constant-factor asymptotic optimality). Their gap is denoted epsilon, and their target error is `2^(-alpha)`.

The paper already supplies fixed-degree compositions with asymptotically optimal multiplicative complexity in the gap and accuracy parameters. Its global Lemma 3 includes the classical cubic `f(x)=(3x-x^3)/2` and states `0 <= 1-f(x) <= (1-x)^(3/2)` on `[0,1]`. Its displayed minimax-degree asymptotic discussion does not itself establish uniformity over every coupled endpoint regime. The separate derivation below uses the global lemma directly instead. These are substantial prior results and must receive explicit credit.

### Chen and Chow (2014)

Jie Chen and Edmond Chow, *A Stable Scaling of Newton-Schulz for Improving the Sign Function Computation of a Hermitian Matrix*, ANL/MCS-P5059-0114, 2014; [primary author report](https://www.mcs.anl.gov/papers/P5059-0114.pdf).

Section 3, equations (3.3)-(3.5), printed p. 9, gives the same optimally scaled cubic used by the candidate. Equation (3.6), printed p. 10, gives the same scalar endpoint update. Theorems 3.1-3.2, printed p. 11, analyze the scalar/matrix iteration and its convergence. Thus neither the scaled cubic nor its endpoint recurrence is a new invention in this submission. I did not find the candidate's specific comparison against an unrestricted multiplication budget in these inspected portions.

### Amsel, Persson, Musco, and Gower, Polar Express

Noah Amsel, David Persson, Christopher Musco, and Robert M. Gower, *The Polar Express: Optimal Matrix Sign Methods and Their Application to the Muon Algorithm*, [arXiv:2505.16932v5](https://arxiv.org/html/2505.16932v5), 4 May 2026.

Theorem 3.1, equations (8)-(10), proves global optimality of the greedy construction within the fixed-degree composition class. It is not an optimization over all unrestricted straight-line programs. Appendix F, equation (17), gives the optimal cubic explicitly; Section 3.2 and Appendix B credit Chen and Chow's antecedent cubic. Theorem 3.3 gives a composition error estimate, but does not state the canonical multiplication-overhead comparison.

For an input interval `[a,1]`, equation (17) uses `alpha=sqrt(3/(1+a+a^2))` and a final centering scalar. Substituting this alpha into `(3 alpha x-alpha^3 x^3)/2` gives exactly the candidate's `g_a(x)`; the centering scalar is exactly `2/(1+phi(a))`. This direct algebraic identification was checked independently.

## A uniform-order corollary from prior estimates

This section is the reviewer's explicit synthesis, not a quotation of a theorem in CKK. It shows why neither a first constant-factor optimal cubic method nor a first known asymptotic order should be claimed.

Keep the canonical definitions and put

$$
r=\frac{1-\delta}{1+\delta},\qquad f(x)=\frac{3x-x^3}{2}.
$$

Iterating the global one-step inequality gives, for every positive integer `T` and every `0 < delta < 1`,

$$
C_T(\delta)\le 1-f^{\circ T}(\delta)
\le (1-\delta)^{(3/2)^T}.
$$

Here `f` is increasing on `[0,1]`, fixes 1, and is odd, so its worst error on the two intervals is the displayed endpoint error. Each iterate stays in `[0,1]`; induction justifies the real exponent at every stage.

The classical Chebyshev comparison, independently proved in Section 2 of the candidate, gives

$$
E_m(\delta)\ge r^{2^m}.
$$

This bound is positive and holds for every allowed program because its polynomial degree is at most `2^m`. There is no assumption that the infimum is attained.

Since

$$
(1-\delta)^2\le\frac{1-\delta}{1+\delta}=r,
$$

the choice

$$
T=\left\lceil\frac{(m+1)\log 2}{\log(3/2)}\right\rceil
$$

implies

$$
C_T(\delta)\le(1-\delta)^{2^{m+1}}
\le r^{2^m}\le E_m(\delta).
$$

This is already a uniform `O(m+1)` upper bound, including arbitrarily small gaps, gaps arbitrarily close to one, and gaps depending on `m`. It avoids substituting endpoint regimes into a fixed-parameter asymptotic theorem.

For completeness, the matching order lower bound also needs no newly invented iteration. First `C_T>0` follows from the same degree lower bound. A linear stage gives `C_T<1` for `T>=1`. If an odd composition has error `e<1`, normalize its output by `1+e`; its positive image lies in `[a,1]`, where `a=(1-e)/(1+e)`. Apply the classical `f`, then center the resulting interval by multiplying by `2/(1+f(a))`. All of this postprocessing is a single allowed cubic stage. It reduces the error to at most

$$
F(e)=\frac{1-f((1-e)/(1+e))}{1+f((1-e)/(1+e))}<e,
$$

because `f(a)>a` for `0<a<1`. Continuity and a minimizing sequence yield `C_(T+1) <= F(C_T) < C_T`. Also `C_1<C_0` follows by using the optimal linear stage. Since `E_m <= C_floor(m/2)`, every `T<floor(m/2)` is excluded. Thus a short synthesis of existing estimates and elementary comparisons yields the uniform order itself.

## What the candidate's sharper comparison does

The candidate establishes the exact factorization

$$
27(1+a)^2(1+a^2)^2-16(1+a+a^2)^3
=(1-a)^2(11a^4+28a^3+30a^2+28a+11).
$$

This implies `phi(a) >= 2a/(1+a^2)`, so the known scaled cubic squares the centered interval error ratio at each step. Coupled with the degree lower bound, the candidate obtains `C_m <= r^(2^m) <= E_m`, hence `T_min <= m`. This improves the explicit constant in the elementary prior-estimate synthesis above. It does not make the cubic, its centering, global optimality within compositions, or constant-factor efficient sign approximation new results.

My source review found no explicit occurrence of this particular ratio comparison or the resulting `T_min<=m` in the inspected sources. It would be unwarranted to turn that observation into a first-discovery claim. The submission can state and prove the bound while withholding a novelty assertion.

## Canonical scope versus the original source

The retained canonical README asks for the asymptotic dependence of `T_min(m,delta)`. In the usual two-sided order-of-growth sense, the candidate answers all of that request: absolute constants work for every nonnegative integer `m` and every `delta` strictly between zero and one. No excluded parameter regime remains.

The broader source [Simons workshop report, arXiv:2602.05394v3, Section 6.3, Problem 6.5](https://arxiv.org/html/2602.05394v3#S6.SS3) asks about the same-budget error comparison and alternatively the smallest stage count. The candidate does not determine its exact integer value, an optimal asymptotic leading constant, or the same-budget error ratio. A notice must explicitly leave those refinements unresolved. The degree-eight follow-up's Section 7 also does not supply the missing unrestricted-budget comparison. Its third author is **Gustaf Lorentzon (G. Lorentzon)**, not H. Lorentzon. [Primary record](https://arxiv.org/abs/2606.24701v1).

Recommended resolution wording: "The canonical asymptotic comparison is resolved: `T_min(m,delta)=Theta(m+1)` uniformly for `0<delta<1`, with `floor(m/2)<=T_min<=m` for `m>=2` and both small cases equal to one. This note gives an explicit comparison using the known scaled cubic, with prior constant-factor composition complexity due to Cheon-Kim-Kim and the scaled iteration due to Chen-Chow; Polar Express gives optimality within the composition class. The exact minimum, optimal leading constant, and same-budget error comparison are not determined."

## Public eligibility and review limits

The single public-network audit finished at `2026-09-12T01:47:54.300055+00:00`. It read all 40 branch heads across five public repositories, 106 selected text blobs, and 32 pull-request review bodies. MF-02 was Open on every head; no matching solution discussion was found. The full snapshot is private `public-network.json`, SHA-256 `a23f5878916bd27b099c66bc86ab91f437b4acf6ff75aa9ff4e39b26ed7bb0ff`. Repository names, head SHAs, selected paths, search scope, and discussion endpoints are recorded by `network_check.py`.

This is evidence about the selected public network and inspected sources at the stated time, not an exhaustive priority certificate. It supports a canonical resolution submission that makes the above scope and attribution explicit. It does not support presenting classical cubic approximation as newly discovered.

I read the complete candidate and canonical statement, checked the relevant primary statements, and independently derived the uniform-order synthesis and the identity of the scaled cubics. The CKK PDF's complete relevant pages 9, 14, 15, 17, and 18 were visually inspected. This report does not certify every theorem or experiment in the cited papers and does not replace the separate adversarial review of the candidate's full proof.

Keep downloaded third-party PDFs, page images, extracted source text, and unredacted network bodies private. Only this original review, a sanitized eligibility record, scripts without credentials, citation metadata, and fingerprints are suitable for copying into a public submission. No canonical file or status was changed by this review.
