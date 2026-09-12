# Independent agent review: RA-13 full trace-tail proof

Reviewer: Codex agent `/root/review_aa01`  
Date: 11 September 2026  
Author of the reviewed proof: George Stepaniants  
Result: **PASS for the complete canonical RA-13 target**, subject to the explicitly cited published bell-shape theorem. This is an independent mathematical agent review, not external human peer review or formal verification.

## Exact reviewed version and scope

- File: `/tmp/nla-fresh-round1/ra13/full-proof-candidate.md`
- Size: 14,786 bytes.
- SHA-256: `6ee4efe2bf23c91276db20bb2bf67ca05c5fa659f30f50b6f8670fd8507d5dff`.
- The reviewed target is the full two-step probability comparison in `randomized-and-low-rank-approximation/RA-13/README.md`, for every nonzero real symmetric matrix, including indefinite matrices, every positive integer sample count, and the stated non-strict threshold. It is not merely a bound on an auxiliary mode or inflection point.

I read the complete candidate, the canonical target, the pinned primary text of Kwaśnicki's Corollary 1.2 and Section 2, and Hallman's Theorem 7, Conjecture 4, and Appendix A.2. I independently rederived the kernel identities and the centered square-transfer derivative rather than relying on the author's summary or a numerical test. I did not write or collaborate on this proof before this review.

The original 14,776-byte draft had hash `0a3e033ae60b44b8d5f551c7bb0730ffd660680b374e4a8666b86326505341f6`. The exact version reviewed here replaces the ambiguous phrase about the artificial zero-scale mass by “place mass 2−C0 at scale zero”; the mathematical formulas are unchanged. One harmless source typo remains in the definition of M,V,R: the two literal `,quad` strings should be `,\quad`. This specific typesetting correction is permitted in publication conversion and does not change the reviewed mathematics. A subsequently rendered manuscript should receive its own exact-source conversion check.

## 1. Published shape theorem: the hypotheses really apply

Kwaśnicki's Corollary 1.2 applies to infinitely divisible densities whose Lévy density ν satisfies complete monotonicity of xν(x) and xν(−x) on x>0. For a component w Gamma(r,1), the corresponding quantity is r exp(−x/|w|) on its jump half-line and zero on the other. Finite positive sums of these exponentials satisfy the hypothesis, with integrability at zero. Shifts and Gaussian components are allowed. Thus the candidate's signed Gamma sums are weakly bell-shaped, and every positive Gaussian convolution is strictly bell-shaped in the source's definition. Its second derivative has exactly two sign changes. These uses match the primary theorem rather than an unproved general assertion about arbitrary infinitely divisible distributions.

For positive Gamma sums of total shape R>2, the standard convolution-simplex representation gives a density of the form constant times x^(R−1) times a positive analytic function near the support endpoint, after translation. Hence the zero extension is C1, the second derivative is locally integrable, and the density is analytic in the interior. Gaussian approximation gives at most two sign changes of the second derivative there, as described in Section 2 of the cited source. The initial second-derivative sign is positive because R>2. A negative sign occurs because the density rises and then must fall; a positive sign occurs later because its negative first derivative tends to zero. The at-most-two-sign-change property then enforces the +,−,+ pattern. These observations also justify identifying the global positive maximum of −f' with the upper transition, without assuming that every zero is a simple zero. Possible isolated zeros without a sign change do not obstruct convexity after that transition.

## 2. Signed distributional kernel identities

For a negative scale w, K2's endpoint jump has negative sign; I checked this explicitly. With K0,i=r_i/|w_i| exp(−|t|/|w_i|) on the appropriate half-line, the identities are exactly

    K2' = −K1 + (sum_i r_i w_i) δ0,
    K2'' = K0 − (sum_i r_i) δ0 + (sum_i r_i w_i) δ0'.

Thus the candidate retains the correct signs for negative scales. The Laplace transform of K2 is sum_i r_i w_i^2/(1+w_i s). Differentiating the centered log transform verifies

    (x−M)f = −τ²f' − K2*f' = τ²g + K2*g,

where g=−f'. The arbitrary shift c is correctly absorbed into M.

At a global positive maximum z of g, g'(z)=0 and g''(z)≤0. Dividing by g(z)>0 is legitimate. Setting ν(t)=1−g(z−t)/g(z) gives a bounded nonnegative function, even when g is negative away from its maximum. The kernel integrals are finite. Direct differentiation gives

    d h0 = τ²+V−B0,
    h0−d = A0,
    C0 = 2+τ² g''(z)/g(z) ≤ 2.

Also C0≥0 from its integral definition. Consequently the additional mass 2−C0 at scale zero is nonnegative. Eliminating h0 yields

    d² + integral (d w+w²) dμ(w) = V+τ²,

with total mass exactly two. No sign is assumed for A0. If b≤0 and d≥−2b, the function d w+w² is nondecreasing for all w≥b, including the artificial zero. The resulting inequality and its rearrangement into (d+b)²≤V+τ²−b² are correct.

For a positive unsmoothed augmented sum, R>2 ensures the endpoint integration-by-parts terms vanish. The same identities are valid at its interior maximum of g. With τ=0, C0=2 exactly, so no zero-scale mass is present; the minimum actual positive coefficient can therefore be used as b. This distinction between the signed smoothed and positive unsmoothed cases is essential and has been handled correctly.

## 3. The selected augmented-density bounds

For the augmentation Z_w+aE1+bE2, the mean is a+b and its Gamma variance is v+a²+b². In the signed case b is the global minimum coefficient and −1≤b<0<a≤1. Under the contradiction hypothesis z>H(v+τ²)>2,

    d = z−a−b > 2−a−b ≥ −2b,

because 2−a+b≥0. The kernel bound then gives (z−a)²≤v+τ²+a². Since z−a>0, taking the positive square root gives z≤a+sqrt(v+τ²+a²)≤H(v+τ²), a contradiction. Thus the density is convex on the required entire upper tail.

In the positive case, all nonzero scales are at least b>0 and a+b≤2, so z>H(v)>2 implies d>0. The unsmoothed version applies and gives the same contradiction. Its total shape is the original positive total shape plus two, and is therefore strictly greater than two for every α>0. This remains true under the later Gamma splitting.

The argument proves convexity only for pairs selected according to these minimum-coefficient conditions. It does not reassert Hallman's disproved auxiliary conjecture about arbitrary pairs.

## 4. Square-transfer sign and grouped removal of negatives

For an interior square transfer a²→a²+t, b²→b²−t, the centered log-Laplace derivative is

    (α/2) s² [1/(1+a s) − 1/(1+b s)]
      = (α/2)(b−a)s³/[(1+a s)(1+b s)].

Dividing by s for the CDF transform therefore gives exactly the candidate's coefficient times the second derivative of the augmented density. This separately verifies the sign in equation (8). It also agrees with Hallman's Appendix A.2 after rate normalization. The signed Gaussian version has an integrable Fourier inversion kernel on compact interior parameter intervals, which justifies differentiation. In the positive unsmoothed version the augmented density and first derivative vanish at the support endpoint and its second derivative is integrable there; the fixed positive thresholds are strictly inside the support. The same identity is valid there. Continuity handles transfer endpoints at which a coefficient vanishes.

For l identical minimum negative coefficients, changing the receiver square at speed l and each negative square at speed −1 is the sum of l legal pair directions. All augmented laws coincide, so their derivatives add to l times (8). The receiver is positive on the open interval even when it starts at zero; the negative group remains a global minimum until it reaches the next negative level. At that point merging all tied coefficients preserves this invariant. The upper tail increases because b−a<0 and the augmented density is convex at the threshold.

The termination argument is finite, not a limiting algorithm hidden in the proof. Each level meeting joins previously distinct negative groups; a positive receiver that reaches one is permanently set aside and there can be at most floor(r) such receivers; if neither happens the last minimum group reaches zero. New zero coordinates are harmless independent Gamma variables with initially zero weight. Sum of squares and the unit coefficient cap are preserved throughout, including the case of an initially all-negative vector.

The path is independent of τ. Taking xτ=h+H(v+τ²)−H(v) and τ↓0 is valid at the non-strict endpoint because all nonzero finite Gamma combinations have continuous distributions. Their variance v stays positive.

## 5. Positive concentration, the Gamma limit, and the exact target

After removing negative coefficients, choose the smallest positive fractional coefficient as donor. All other nonfractional positive coefficients are one, so it is also the global positive minimum required by the bound. Transferring its square to another fractional coefficient preserves that property. Each stage makes a coefficient zero or one, so finitely many stages yield the asserted vector of floor(r) ones and a single square-root remainder. These arguments establish the first one-sided comparison for every common shape α>0.

Splitting each Gamma(α,1) variable into N independent Gamma(α/N,1) variables preserves its law. The repeated coefficient vector has squared norm Nr but variance v unchanged. Concentration at common shape α/N yields a Gamma term with shape cN=(α/N)floor(Nr)→v and a centered residual of variance at most α/N. Thus the endpoint converges in distribution to Gamma(v,1)−v. Continuity of its CDF permits the limit at every asserted h, including h=H(v). Applying this result to the concentrated vector itself gives the second inequality in the displayed chain, not merely a separate bound for the original vector.

Applying the first comparison to −w bounds the lower tail by the same positive concentrated law. Because h>0, the two tail events are disjoint and their probabilities add. The coefficient normalization α=m/2, w_i=λ_i(A)/||A||2 and the factor 2||A||2/m exactly convert the chi-square representation of the Gaussian trace estimator to the candidate. The canonical Gamma rate, centering, extremal matrix spectrum, and displayed threshold all agree. Zero padding, integer r, arbitrary sample count, and indefinite or zero-trace A are included. A itself is assumed nonzero as in the canonical statement.

## Review conclusion and limits

No unresolved mathematical gap was found in the complete proof. The external bell-shape theorem is used within its stated scope; the new inflection identity and selected transfer path supply the missing threshold argument. This is a full affirmative proof of the canonical RA-13 probability chain, conditional only in the ordinary sense of relying on that published theorem. It does not rehabilitate the separately refuted auxiliary inflection conjecture.

This review does not establish historical priority, certify the status of every remote branch, or authorize a public submission. Root is handling the current repository-status audit and the submission workflow. Final publication files should preserve this proof, fix the noted typesetting typo, retain the auxiliary-result attribution on the canonical page, and receive a separate source-conversion/PDF check.

## Primary sources actually checked

- Mateusz Kwaśnicki, *A new class of bell-shaped functions*, arXiv:1710.11023v3, Corollary 1.2 and Section 2: https://arxiv.org/html/1710.11023v3
- Eric Hallman, *Extremal bounds for Gaussian trace estimation*, arXiv:2411.15454v1, Theorem 7, Conjecture 4, and Appendix A.2: https://arxiv.org/html/2411.15454v1
