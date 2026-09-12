# RA-12 — Relative-error threshold for extremal Gaussian trace bounds

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because an explicit threshold must control extremal tails uniformly over spectra; community impact is sharper distribution-level trace-estimation confidence bounds.  
**Source:** Hallman, Conjecture 3 together with Theorem 6.  
**Last checked:** 2026-09-11  
**Status:** Solved

## Affirmative resolution - 11 September 2026

**Author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. **Independent Codex-agent review: PASS.**

[The complete proof](solution.md), **Theorem 1, Lemmas 2-4 and the final proof of Theorem 1**, proves both comparisons in the original probability chain for every nonzero real positive semidefinite matrix, every integer $m\ge1$, every effective rank $\mu$, and every $\varepsilon\ge2/(m\mu)$, including equality at the stated threshold. Each one-sided tail is compared separately. No case of the canonical target remains open; optimality of the threshold is not asserted.

The proof chooses coefficient transfers whose smaller augmented scale is a minimum positive scale, applies an elementary Gamma-density mode bound and classical Gamma-convolution unimodality, and uses infinite divisibility for the Gamma endpoint. The primary unimodality input is Roosta-Khorasani and Székely, Appendix A, Theorem 4; the coefficient derivative is also credited to Hallman, Appendix A.1.

[Proof PDF](solution.pdf) · [Standalone TeX](solution.tex) · [Independent proof review](../../references/stepaniants-ra12-2026-09-11/verification/RA-12-independent-review.md) · [Authorship, frozen sources and submission record](../../references/stepaniants-ra12-2026-09-11/README.md).

The work was developed with substantial ChatGPT/Codex assistance. Verification is independent agent review, not external human peer review or formal certification. The original statement, ID and earlier results below are retained. The difficulty and importance ratings are historical; this solved entry no longer contributes to the open count.

<!-- colbrook-transfer -->
## Related auxiliary counterexamples — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent Codex-agent review: PASS for the limited result below.**

The submitted Gamma-density examples refute the upper-mode assertion in Hallman Conjecture 1 and the upper-inflection assertion in Conjecture 2, with legally distinct augmentation indices. These are counterexamples to auxiliary assertions.

**Historical scope of the auxiliary submission:** These examples did not prove or refute the complete relative Gaussian trace-tail probability chain and did not establish a revised sharp tail threshold. They left RA-12 open at that stage. The full affirmative resolution above settles that remaining target while preserving these auxiliary counterexamples and their attribution.

**Primary reference:** [complete authored PDF](../../references/colbrook-transfer-2026-09-11/manuscripts/04_gamma_auxiliary_counterexamples.pdf), [standalone TeX](../../references/colbrook-transfer-2026-09-11/manuscripts/04_gamma_auxiliary_counterexamples.tex), **Proposition 2.1 (with Proposition 3.1 for related evidence)**. [Independent proof review](../../references/colbrook-transfer-2026-09-11/verification/reviews/gamma-auxiliary-review.md) · [Authorship and submission record](../../references/colbrook-transfer-2026-09-11/README.md). Verification is independent agent review, not external human peer review or formal certification.

<!-- /colbrook-transfer -->

\newpage

## Problem statement

For a real symmetric $d\times d$ matrix $D$ and integer $m\ge1$, define the Gaussian trace estimator

$$
T_m(D)=\frac1m\sum_{j=1}^{m}z_j^TDz_j,
\qquad z_1,\ldots,z_m\overset{\mathrm{iid}}{\sim}N(0,I_d).
$$

Let $A\ne0$ be any real symmetric positive semidefinite $n\times n$ matrix, with $n\ge1$, and set

$$
\mu=\frac{\operatorname{tr}(A)}{\|A\|_2},\qquad
B_\mu=\frac1\mu\operatorname{diag}
\left(I_{\lfloor\mu\rfloor},\,\mu-\lfloor\mu\rfloor\right).
$$

Here $\|\cdot\|_2$ is the spectral norm, $\mu\ge1$, and a zero final diagonal entry may be retained. Let $X$ have the Gamma distribution with shape and rate both $m\mu/2$. The shape/rate convention means that $\operatorname{Gamma}(\alpha,\beta)$ has density $\beta^\alpha x^{\alpha-1}e^{-\beta x}/\Gamma(\alpha)$ for $x>0$.

**Conjecture.** For every such $A$, every integer $m\ge1$, and every $\varepsilon\ge2/(m\mu)$, the complete comparison chain holds:  
$$
\begin{aligned}
\Pr\!\left(
 |T_m(A)-\operatorname{tr}(A)|
 \ge\varepsilon\operatorname{tr}(A)
\right)
&\le \Pr\!\left(|T_m(B_\mu)-1|\ge\varepsilon\right)\\
&\le \Pr\!\left(|X-1|\ge\varepsilon\right).
\end{aligned}
$$

Each estimator uses Gaussian vectors of its own matrix dimension; only their distributions are compared.

## Why it matters in numerical linear algebra

This would specify the tolerance range on which effective rank yields extremal, distribution-level confidence bounds for Gaussian trace estimation. It also applies to Frobenius-norm estimation through $\|C\|_F^2=\operatorname{tr}(C^TC)$.

## References

1. Eric Hallman, [*Extremal bounds for Gaussian trace estimation*](https://arxiv.org/html/2411.15454v1#S5), arXiv:2411.15454v1 (2024), §5, Theorem 6 and Conjecture 3.
2. Alice Cortinovis and Daniel Kressner, [*On Randomized Trace Estimates for Indefinite Matrices with an Application to Determinants*](https://doi.org/10.1007/s10208-021-09525-9), FoCM 22 (2022), 875–903, Theorem 1.

## Historical status check

Theorem 6 proves the comparisons beyond an unspecified threshold; Conjecture 3 supplies the explicit threshold above. On 2026-09-08 the [arXiv record](https://arxiv.org/abs/2411.15454) still listed only v1. Title, author, conjecture-number and 2025/2026 searches found no resolution. The author's [later XTrace paper](https://arxiv.org/abs/2512.02316) studies different estimators. This is a bounded check.

## Audit — 2026-09-10

Rechecked [Hallman, Theorem 6 and Conjecture 3](https://arxiv.org/html/2411.15454v1); the record still lists only v1. Author, Gaussian-trace, and conjecture searches found no resolution. An unspecified larger threshold proves a weaker result and does not verify the displayed explicit threshold.

## Resolution audit - 11 September 2026

The complete proof passed independent Codex-agent review against the unchanged canonical target. A [public-network check](../../references/stepaniants-ra12-2026-09-11/verification/network-check-latest.json) at 19:20:50 UTC inspected all 21 branch heads across the parent repository and its four recursively reported public forks, canonical and ID-named text documents, and upstream issues, pull requests and comments. RA-12 remained Open on every checked branch; [PR 32](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/32) and [issue 31](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/31) concern the retained auxiliary counterexamples. No competing complete solution was found in this bounded public check; private, deleted and unpublished work was outside its scope.
