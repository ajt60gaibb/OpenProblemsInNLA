# MD-05 — The sharp universal Spencer discrepancy constant

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Provenance:** source-stated extremal-value problem.  
**Status:** Open  
**Last checked:** 2026-11-27

**Rating rationale:** Determining the best constant across all sign matrices and all orders is a longstanding extremal discrepancy barrier; it sharpens a central matrix-balancing theorem.


For each positive integer $`n`$, define

```math
d_n=\frac{1}{\sqrt n}
\max_{A\in\{-1,1\}^{n\times n}}
\min_{x\in\{-1,1\}^n}\|Ax\|_\infty.
```

Determine the exact value of

```math
C_*=\sup_{n\geq1}d_n.
```

Thus $`C_*`$ is the smallest real constant for which every square sign matrix $`A`$ admits a column signing $`x`$ with $`\|Ax\|_\infty\leq C_*\sqrt n`$.

The question concerns the sharp worst-case error in simultaneous signed sums. In matrix form it asks how far a square sign matrix can keep all sign vectors from the coordinate cube of radius $`C\sqrt n`$.

The source also poses $`\limsup_{n\to\infty}d_n>1`$ as a related asymptotic conjecture. It is recorded here as context rather than counted as another entry.

## References

1. A. S. Bandeira, A. Kireeva, A. Maillard, and A. Rödder, *Randomstrasse101: Open Problems of 2024*, arXiv:2504.20539 (2025), entry 6, Open Problem 11, Conjecture 12, and the subsequent “Updates” paragraph. [Paper](https://arxiv.org/html/2504.20539v1).
2. A. S. Bandeira, *Did just a couple of deviations suffice all along? (problems 10–14)*, Randomstrasse101 (2024), the original statement of Open Problem 11. [Author's research post](https://randomstrasse101.math.ethz.ch/posts/HowManyDeviations/).
3. J. Spencer, *Ten Lectures on the Probabilistic Method*, second edition, SIAM (1994), Chapter 10, “Six Standard Deviations Suffice,” pp. 75–80, the classical universal-constant upper bound. [Chapter](https://epubs.siam.org/doi/10.1137/1.9781611970074.ch10).
4. V. Reis and Z. Song, *Three Standard Deviations Suffice While One Does Not*, arXiv:2609.34471v1 (2026), Theorems 1.1 and 1.2. [Preprint](https://arxiv.org/html/2609.34471v1).
5. Y. Li, order-17 sign-matrix certificate (2026). [Explicit matrix](https://teorth.github.io/optimizationproblems/constants/10c.html).

## Status check — 2026-11-27

Reis and Song's Theorem 1.1 gives $`\limsup_{n\to\infty}d_n>1.0000002`$, establishing the source's related Conjecture 12. Theorem 1.2 gives $`d_n\leq\sqrt{3\mathop{\mathrm{arsinh}}\nolimits(10)}+4/\sqrt n`$ for every $`n`$. Combined with exact binomial counting, this gives a uniform upper bound on $`C_*`$.

```math
\frac{7}{\sqrt{17}}=d_{17}\leq C_*\leq\sqrt{10}.
```

The exact value of $`C_*`$ remains open.

## Verification of the bounds

For a fixed sign row and a uniformly random signing, the probability that the absolute row sum is at least a positive integer $`b`$ of parity $`n`$ is

```math
\mathbb{P}(|(Ax)_i|\ge b)=2^{1-n}\sum_{j=0}^{(n-b)/2}\binom{n}{j},
```

where the sum is empty if $`b>n`$. If $`n`$ times this probability is strictly below one, some signing has all absolute row sums below $`b`$.

At $`n=17`$, the count with $`b=9`$ is $`34\sum_{j=0}^4\binom{17}{j}=109276<2^{17}`$. Parity gives $`d_{17}\le 7/\sqrt{17}`$. For the opposite inequality, use Li's sign matrix. The verification below encodes each row by the bit mask of its negative entries. A signing with mask $`x`$ has absolute row sum $`|17-2\,\mathop{\mathrm{popcount}}\nolimits(x\mathbin{\oplus}r)|`$ against row mask $`r`$.

For the upper bound on $`C_*`$, Reis and Song give discrepancy strictly less than $`3\sqrt n+4`$, since $`\sqrt{3\mathop{\mathrm{arsinh}}\nolimits(10)}<3`$. For $`n\ge608`$, we have $`4/\sqrt n<\sqrt{10}-3`$. For $`1\le n<608`$, take $`b`$ to be the least integer greater than $`\sqrt{10n}`$ of parity $`n`$. Either the binomial count yields a signing with maximum below $`b`$, or $`3\sqrt n+4\le b`$ so the preprint's bound gives such a signing. In both cases parity gives $`d_n\le\sqrt{10}`$. The following checks the witness and all 607 small orders using exact integers.

```
from math import comb, isqrt

rows = (
    0x0, 0x7F, 0x787, 0xBB8, 0x15D9, 0x1ACE,
    0x1D62, 0x1E35, 0x26F2, 0x29E5, 0x2D1E, 0x2E49,
    0x332B, 0x3354, 0x34AC, 0x3893, 0x0,
)
assert min(
    max(abs(17 - 2 * (x ^ row).bit_count()) for row in rows)
    for x in range(1 << 17)
) == 7

for n in range(1, 608):
    b = isqrt(10 * n) + 1
    b += (n - b) % 2
    tail_count = sum(comb(n, j) for j in range((n - b) // 2 + 1))
    union_bound = 2 * n * tail_count < (1 << n)
    preprint_bound = b >= 4 and (b - 4) ** 2 >= 9 * n
    assert union_bound or preprint_bound, (n, b)
```

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
