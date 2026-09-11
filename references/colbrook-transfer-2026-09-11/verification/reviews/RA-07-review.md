# Independent review: RA-07

**Verdict: PASS for the exact canonical RA-07 question and all mathematical corollaries in the original manuscript.** No mathematical repair is required. This is an independent Codex subagent audit, not human peer review or a certification of publication priority.

Review date: 2026-09-11. Reviewer task: `/root/review_transfer_volume_learning`. The complete original manuscript, including its application, stable-rank bounds, scope paragraph, and bibliography, was read together with the complete common preamble. The adjacent canonical README and generated problem TeX were both checked. The verdict comes from the proof audit below, not from the submitted verification programs.

## Artifact identity

Hash convention: read the entire UTF-8 source, replace CRLF by LF, encode UTF-8, and compute SHA-256. No trimming, whitespace rewriting, or removal of the final newline is performed.

| Artifact | Normalized bytes | Normalized SHA-256 |
| --- | ---: | --- |
| `.cache/colbrook-transfer-submission/nla_submission/manuscripts/01_volume_sampling_convexity.tex` | 8814 | `14cce6c0d191808532ea6ddf8890eaf365d845477df9fdbcc102d7e79791f800` |
| `.cache/colbrook-transfer-submission/nla_submission/manuscripts/common_preamble.tex` | 1105 | `8b784fe6ac56151b19d51534474560bf45df7b278015cd0c834569e2550fada4` |

The common preamble introduces ordinary norms, inner products, theorem environments, and notation; it adds no mathematical assumptions. This review is anchored to the above complete original, not an excerpt or a later reformulation.

## Exact target match

Canonical target: `randomized-and-low-rank-approximation/RA-07/README.md` and `problem.tex`, as present when reviewed. It asks whether, for every positive tuple of length at least three, the sequence `(j+1)e_{j+1}/e_j`, indexed by `1 <= j <= n` with `e_{n+1}=0`, has nonnegative second differences at `2 <= j <= n-1`.

The manuscript proves the identical inequality on the larger index set `0 <= j <= n`, including second difference `j=1`, and proves strict decrease. Thus its stronger endpoint convention covers the canonical question without changing its quantifiers or the meaning of the error. It does not substitute convexity of a continuous rational function, convexity of a logarithm, or an optimized approximation ratio.

The primary source's Section 5 states this elementary-symmetric-ratio conjecture and explains the intended Jensen consequence; its Theorem 1 defines the same stable-rank comparison function. These are the relevant historical targets. [Dereziński, Khanna, and Mahoney, arXiv:2002.09073v3](https://arxiv.org/html/2002.09073v3)

## Complete proof audit

### Polynomial reduction and endpoint handling

For `P(t)=product_i(1+lambda_i t)`, the exact coefficient relation is `P^(j)(0)=j! e_j`, hence `F_j=P^(j+1)(0)/P^(j)(0)`. Every root of P is strictly negative. Rolle's theorem, with repeated roots counted with their reduced multiplicities, places every root of every nonconstant derivative within the negative root interval. The leading coefficient and the value at zero are positive. Therefore `Q=P^(k-1)` has the claimed factorization with positive reciprocal-root parameters `mu_a`.

For a second difference, Q has degree `n-k+1 >= 2`. Expanding its first three derivatives at zero yields, with `D=s_1^2-s_2`,

```text
F_(k-1) = s_1
F_k     = D/s_1
F_(k+1) = (s_1^3 - 3 s_1 s_2 + 2 s_3)/D.
```

Independently putting these terms over denominator `s_1 D` gives numerator

```text
s_1^2 D - 2 D^2 + s_1(s_1^3 - 3s_1s_2 + 2s_3)
= 2s_1s_3 - 2s_2^2.
```

The denominator is strictly positive because `D=2 sum_(a<b) mu_a mu_b`. Pairing the off-diagonal terms in `s_1s_3-s_2^2` gives `sum_(a<b) mu_a mu_b (mu_a-mu_b)^2`. This is the exact asserted nonnegative certificate. At `k=n-1`, Q is quadratic, its third derivative is zero, and the same calculation remains valid; there is no division by a vanished third derivative.

Using `Q=P^(j)` instead gives `F_j-F_(j+1)=s_2/s_1>0`. For a linear Q this equals its sole positive reciprocal-root parameter, and the next sequence value is exactly zero. Equal eigenvalues give `F_j=(n-j)lambda` and equality in every second difference. These checks verify the important repeated-root and terminal-index cases.

### Fixed-size and random-size determinantal identities

For `0 <= j <= rank(A)`, the principal-minor sum is `e_j` of the positive eigenvalues of `A^T A`. The Gram determinant update is valid for nonsingular selected columns by the squared-volume formula. For singular selections, adding one vector can increase rank by at most one, so a formerly singular j-set still cannot produce a nonsingular `(j+1)`-set. Both sides of the update are therefore zero. The empty set has determinant one and the zero projector, so the argument includes `j=0`.

Summing the update counts each `(j+1)`-set exactly `j+1` times, yielding `E_j error=F_j`. This remains correct at `j=rank(A)`, where the error vanishes. With `t=1/alpha`, the random-size normalizer is P(t); the size expectation is `tP'(t)/P(t)` while the error expectation is `P'(t)/P(t)`. Their ratio is alpha, producing precisely the two displayed random-size identities.

Conditioning on the sampled size recovers the corresponding fixed-size distribution. Piecewise-linear interpolation of the established sequence has increasing slopes and is decreasing. Consequently, for `E K <= k`, both inequalities in `F(k) <= F(E K) <= E F(K)` have the correct direction. The scalar size expectation is continuous and strictly decreasing from r to zero as alpha increases, giving exactly one positive alpha with mean k for `0<k<r`.

### Stable-rank theorem, all three bounds

Writing `ell=k-s`, `beta=lambda_(s+1)`, and `T=sum_(i>k)lambda_i`, split the size sum into its first s terms, its next ell terms, and its tail. The bounds `1`, `beta/(beta+alpha)`, and `lambda_i/alpha` give

```text
mu(alpha) <= s + ell beta/(beta+alpha) + T/alpha.
```

The chosen positive root solves `ell alpha^2=T(alpha+beta)`, so the last two terms sum exactly to ell. Applying the Jensen corollary yields the first bound, with the factor `k/[2(k-s)]` intact. The tail estimate `T >= beta(r_s-ell)` follows directly from bounding each of the intervening eigenvalues by beta. Also `r_s <= r-s`, so the theorem's condition `s<k<t_s` already ensures `k<r` and `T>0`; no zero relative denominator is hidden.

Substitution gives the second bound. Squaring the final scalar inequality reduces it to `sqrt(1+4x) <= 1+2x`, true for `x>=0`. All three inequalities therefore have the stated direction and domain. The final expression equals the source's Phi function, with its concentration multiplier and auxiliary gap restriction removed. This conclusion is proved directly in this manuscript; it is not inferred merely from the conjecture's informal motivation.

The additional worst-case bound is correct: every `(k+1)`-fold distinct product includes at least one index larger than k, and its appearance in `T_k e_k` has coefficient at least one. Other terms in that expansion are nonnegative. Thus `e_(k+1) <= T_k e_k` and `F_k <= (k+1)T_k`.

## Independent diagnostic

As a supplementary check separate from the supplied scripts, a fresh Python standard-library `fractions.Fraction` enumeration computed all elementary symmetric coefficients by descending-degree multiplication for all 1092 tuples in `{1/3,1,5}^n`, `1 <= n <= 6`. It checked strict decrease through the zero endpoint and every defined second difference using exact rational arithmetic. All checks passed. This covers unequal, repeated, and constant tuples; it does not replace the universal proof above. The certificate itself was checked by the explicit symbolic numerator reduction above.

## Scope and limitations

- The exact canonical positive-tuple conjecture is fully covered. Rank-deficient applications use only positive eigenvalues, as the manuscript says.
- Fixed-size sampling above the rank is not asserted. A relative error ratio at the rank endpoint is not asserted. A rank-zero matrix is trivially zero and does not require the theorem.
- The stable-rank and worst-case corollaries are expectations for the stated sampling law; the manuscript does not establish a high-probability analogue or a faster sampling implementation.
- No counterexample or proof gap was found in any mathematical claim of the original. The independent verification does not establish historical novelty, exhaustive literature coverage, or a human authorship claim.
- No canonical problem file or proof source was edited by this reviewer, and nothing was published.
