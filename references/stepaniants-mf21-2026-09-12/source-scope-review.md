# MF-21 independent source and scope audit

Reviewer: separate Codex agent `/root/prepare_manuscripts`.
Checked: 12 September 2026, 03:32 UTC.

**Source/scope verdict: the canonical page accurately identifies a three-part, all-order conjecture. No complete later resolution was located in this bounded primary-source search. This is not yet a verdict on the new candidate proof.**

The exact canonical page inspected is preserved as [canonical-target.md](canonical-target.md), 4,518 bytes, SHA-256 `1aac38ed3c7a83dfc3dddb4beeec26fcf117f23f5789b2a374c1332ba4cf359f`. It is marked Open. This report neither changes that page nor proves the absence of an undiscovered resolution. Search details and primary locators are recorded in [source-search-record.json](source-search-record.json).

## Exact target and review requirements

For every fixed integer $m\ge3$, the symbol is $g_m(\theta)=(2\sin(\theta/2))^{2m}$ and the matrix is its $n\times n$ Toeplitz finite section, with eigenvalues in increasing order. The question asks for **one family** of real continuous functions $d_0,\ldots,d_{2m}$ on the closed interval $[0,\pi]$, independent of matrix size and eigenvalue index, with $d_0=g_m$.

All expansions use precisely $j\pi/(n+2)$ and powers of $(n+2)^{-1}$. They must satisfy all three conditions:

1. At every order $0\le p\le2m-1$, the remainder is uniformly $O((n+2)^{-p-1})$ for every eigenvalue index $1\le j\le n$.
2. At order $2m$, the remainder is uniformly $O((n+2)^{-2m-1})$ for all $\lceil(\log(n+2))^2\rceil\le j\le n$.
3. At order $2m$, that same bound cannot hold uniformly over all $1\le j\le n$.

Constants and starting sizes may depend on $m$ and expansion order, but not on $n$ or $j$. The first two assertions require upper bounds and the third requires a genuine obstruction; neither numerical edge asymptotics alone nor a bulk expansion on $\epsilon n\le j\le(1-\epsilon)n$ completes the target. A different denominator or index convention must be explicitly converted, including its effect on every coefficient and error. A proof with smooth coefficients would imply the stated continuity, but coefficients depending on $n$ or $j$ separately would not.

## Original source and credited results

[Barrera–Böttcher–Grudsky–Maximenko, arXiv:1710.05243v1](https://arxiv.org/pdf/1710.05243v1), Conjecture 8.4 on printed page 26, equation (8.4), states the same threshold and logarithmic cutoff. The canonical page makes explicit the common continuous coefficient convention used in the source. Theorem 1.2 proves the corresponding fourth-order-zero case $m=2$, which is outside MF-21's displayed range. Its positive assertion at order three and failure at order four therefore supply prior background, rather than a resolution of the present all-$m$ target. The arXiv record still lists only version 1, submitted 14 October 2017; the published chapter appeared in 2018.

[Barrera–Grudsky–Stukopin–Voronin](https://link.springer.com/article/10.1007/s43036-024-00374-1), published 4 September 2024, concerns the seventh-diagonal/sixth-order-zero case. Its [full preprint](https://arxiv.org/pdf/2111.07196v1), Theorems 2.3–2.6, uses distinct bulk and endpoint formulas, including implicit index-dependent phases. Its symbol $(t-2+t^{-1})^3$ has the opposite sign to $g_3$ on the unit circle, and its natural shift is $n+3$; these conventions matter when citing particular eigenvalue formulas. The displayed results are not the full common-coefficient assertion through order six, and a result confined to $m=3$ would not settle all $m\ge3$ in any event. This paper must retain its original authors' credit.

[Böttcher's 2026 survey](https://link.springer.com/article/10.1007/s10958-025-07833-x), published online 25 July 2025, separates the higher-order-zero regime in “Beyond the simple-loop class.” Theorems 2–5 describe the fourth-order case, including its endpoint eigenvalue constants, and the subsequent discussion distinguishes higher-order singularities and local asymptotics. I did not find a complete all-$m$ three-part theorem there. Its reference 35, which might initially look like a general extension, is specifically a fourth-order-zero paper; its reference 42 cites an earlier version of Rambour than the version checked below.

## Later results checked directly

[Rambour, arXiv:2101.11250v9](https://arxiv.org/pdf/2101.11250v9), revised 1 December 2025, is newer than the survey's version-8 citation. I checked its Theorems 1 and 2 and Remark 3 on printed pages 2–3. Theorem 1 gives a local expansion with two correction terms and error $O((N+2)^{-3})$ on a fixed interior monotonicity interval. Remark 3 discusses higher powers on intervals bounded away from their endpoints. Theorem 2 extends to all eigenvalues with the additional condition $f''(0)>0$; since $g_m''(0)=0$ for $m\ge2$, it does not cover the canonical family. No all-order logarithmic-cutoff result is stated in this latest version.

[Barrera–Grudsky's rational-symbol paper](https://www.tandfonline.com/doi/full/10.1080/17476933.2021.1963711), published online in 2021 and in volume 67 (2022), explicitly concerns a unique zero of order four. I checked its primary title and publisher abstract. Its extension of the class of symbols does not extend the zero's order to arbitrary $2m$.

The [March 2026 eigenvalue-superposition paper](https://link.springer.com/article/10.1007/s10958-026-08227-3) assumes simple-loop principal symbols in its model and main results. The corresponding positive second derivative at the zero excludes $g_m$ for $m\ge2$. It therefore does not provide the missing high-order endpoint expansion merely because it gives high-order expansions for other Toeplitz sequences.

## Audit limits and independence

The title, conjecture-number, higher-order-zero, and recent-year searches listed in the JSON record did not locate a later complete resolution. This report uses primary papers or their publisher records for its substantive conclusions. A bounded source search cannot establish universal novelty or openness, and this checkpoint is not a fresh exhaustive public-fork inventory.

I requested the author's complete frozen manuscript and its SHA-256 before mathematical review. I have not contributed an argument to it, rewritten it, or treated an outline as verification. A later signed mathematical report must bind its verdict to the actual complete source and explicitly check all three assertions, the upper spectral endpoint, fixed-index extremes, eigenvalue numbering, error uniformity, and every coefficient's endpoint regularity.

Signed electronically by the separate Codex reviewing agent `/root/prepare_manuscripts` on 12 September 2026. This is an AI source/scope audit, not external human peer review or formal verification.
