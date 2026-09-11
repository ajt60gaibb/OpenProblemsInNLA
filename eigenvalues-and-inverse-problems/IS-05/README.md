# IS-05 — The optimal decay exponent for the conditioning of sign matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-09-11  

**Rating rationale:** Extreme reflects a sharp asymptotic rate tied to longstanding gaps in Hadamard constructions; community impact is a quantitative limit on nearly orthogonal sign matrices.

## Partial bound — 2026-09-11

**Partial bound by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. [Complete manuscript](solution.md) · [PDF](solution.pdf) · [LaTeX](solution.tex). **Theorems 1–2 and equations (4)–(8).**

The odd-order obstruction proves $\alpha_*\le1/2$ by an all-orders Gram-matrix variance argument. Theorem 2 also strengthens the condition-number lower bound for $n\equiv2\pmod4$. Combined with the previously recorded construction bound, the interval is $17/92\le\alpha_*\le1/2$. The exact value of $\alpha_*$ and a matching exponent construction remain open; this entry continues to count as open.

The complete argument received an independent Codex-agent **PASS** (partial result only) on 11 September 2026. The [review report](../../references/colbrook-additional-2026-09-11/verification/reviews/IS-05-review.md) records the exact scope and a hash of the original reviewed manuscript. The mathematical sections remain unchanged in the authored version. Original ChatGPT generation is disclosed; no external human peer review or formal proof certificate is asserted. [Submission and verification record](../../references/colbrook-additional-2026-09-11/README.md).

The difficulty and importance ratings still apply to the surviving exact-exponent question.

The review also checked [Alexeev–Jasper–Mixon, version 2](https://arxiv.org/html/2511.14653v2), dated 18 August 2026, §5, Problem 11; it retains the earlier construction exponent and obstruction.

## Context and notation

For $n\geq1$, define

$$
h(n)=\min_{A\in\{-1,1\}^{n\times n}}\kappa_2(A),\qquad
\kappa_2(A)=\frac{\sigma_{\max}(A)}{\sigma_{\min}(A)},
$$

with $\kappa_2(A)=+\infty$ for singular $A$.

## Problem statement

Determine the exact number

$$
\alpha_*=\sup\{\alpha\geq0:\ \exists C>0\ \forall n\geq1,
\ h(n)-1\leq Cn^{-\alpha}\}.
$$

The constant $C$ may depend on $\alpha$, but not on dimension. This
specifies the uniform asymptotic power exponent; logarithmic factors do not
change the supremum. Orders admitting exact Hadamard matrices have
$h(n)-1=0$, which are included without taking logarithms of zero.
Before the 2026-09-11 update above, the recorded bounds were $17/92\leq\alpha_*\leq1$.

## References

Alexeev, Jasper, and Mixon,
[*Asymptotically optimal approximate Hadamard matrices*](https://arxiv.org/html/2511.14653v1),
§6, Problem 11; the supremum above is an editorial precise formulation of
its decay-exponent question. Steinerberger,
[*Open Problems*](https://faculty.washington.edu/steinerb/openproblems.pdf),
Problem 69, November 2025 update, identifies the sharp rate as unresolved.

## Earlier status check — 2026-09-08

Searches for `approximate Hadamard 17/92 2026` and
`approximate Hadamard condition 2026 sharp` found no exact exponent. A global
constant as in [IS-04](../IS-04/README.md) does not specify a decay exponent, while an asymptotic
exponent permits finitely many exceptions to any proposed sharp constant.
The two independently posed problems are therefore retained separately.

## Audit update — 2026-09-10

Rechecked [Alexeev–Jasper–Mixon](https://arxiv.org/html/2511.14653v1), §6, Problem 11, and [Steinerberger's problem collection](https://faculty.washington.edu/steinerb/openproblems.pdf), Problem 69. Both leave the sharp rate unresolved. Searches for later approximate-Hadamard conditioning exponents found no determination of the optimum; a nonsharp exponent bound does not by itself resolve the target.
