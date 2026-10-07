# RA-14 — Optimal query complexity of spectral rank-$`k`$ approximation

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Rating rationale:** Extreme because matching information bounds for every adaptive algorithm and growing rank is a fundamental barrier; broad impact includes large-scale spectral computation and data analysis.  
**Source:** Bakshi–Narayanan, Open Question 1.10.  
**Last checked:** 2026-10-06  
**Status:** Partially resolved  

## Later literature — checked 6 October 2026

The [primary arXiv abstract of Zhang et al.](https://arxiv.org/abs/2609.35840),
first submitted 24 September 2026, reports the spectral query bound

```math
Q_\infty^*=\widetilde\Theta\!\left(
\min\{N,k\varepsilon^{-1/2}\}\right),
\qquad N=\min\{m,n\}.
```

The paper uses adaptive exact products with a real $`m\times n`$ matrix
and its transpose, a rank-$`k`$ right projector, and success probability
$`2/3`$. Its abstract specifies sufficiently small $`\varepsilon`$ and
suppresses logarithmic factors in $`\widetilde\Theta`$.

This supplies relevant growing-rank bounds. However, the repository asks
for **universal constant factors simultaneously in every admissible finite
parameter**, with success probability $`99/100`$. The displayed rate does
not settle the logarithmic factors or by itself close the finite-accuracy
transition gap recorded below. Its success guarantee is not silently
identified with the catalog's guarantee. **Status remains Partially
resolved**, and the original target is unchanged. The paper's Schatten-norm
transition is recorded in [RA-15](../RA-15/README.md).

**Evidence limit:** this check retrieved the primary abstract through the
search index; the full manuscript could not be retrieved. No theorem
number, independently checked full proof, or Lean verification is claimed
for this addition. The earlier partial results and their separate review
records remain as recorded below.


## Further partial results — exact capacity and adaptive innovations, 14 September 2026

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. [Verified affiliation and submission record](../../references/holden-further-2026-09-14/README.md).

[Sections 2–7](../../references/holden-further-2026-09-14/RA-14/manuscript.pdf) give exact minimum-energy certificates, including singular tail features, a Gaussian nodal-capacity formula, a first-moment success bound, and an innovation-qualified adaptive-query tradeoff. An innovation is a query direction outside the span of previous queries and responses. The probability bound applies to success together with a bounded number of innovations; it does not bound every unrestricted algorithm's total query count. The linear-size reduction keeps adaptive dependence, and the full-prefix saturation result explains a limitation of that enlarged comparison space.

A separate [independent Codex AI-agent audit](../../reviews/2026-09-14-further-submissions/RA-14-review.md) passed these new, explicitly qualified partial results. All 24 component tests and the exact rank certificate passed; finite diagnostics supplement the written probability arguments. Earlier packages' unrestricted bounds are outside this fresh audit, and their prior canonical notices remain separate. **The simultaneous finite-parameter characterization remains open**: the continuation does not close the transition gap at $`k=1`$, $`\varepsilon=(\log n/n)^2`$. Status remains Partially resolved.

[Proof source](../../references/holden-further-2026-09-14/RA-14/manuscript.tex). AI assistance is disclosed; no Lean verification, external human peer review, formal verification or novelty claim is asserted. Original assumptions, quantifiers, target, ID and path are preserved.


## Problem statement

Let $`n\ge2`$, $`1\le k< n`$, and $`0<\varepsilon<1/2`$. An unknown matrix $`A\in\mathbb R^{n\times n}`$ is available through exact products $`Ax`$ and $`A^Tx`$, with one such product counting as one query. An algorithm may choose each real query vector adaptively using all earlier answers and its random bits. Arithmetic and other computation between queries are unrestricted; matrix entries are not otherwise accessible.

Let $`q_{\mathrm{sp}}(n,k,\varepsilon)`$ be the smallest integer $`q`$ for which an algorithm using at most $`q`$ queries returns a matrix $`Z\in\mathbb R^{n\times k}`$ with $`Z^TZ=I_k`$ such that, for every input $`A`$,

```math
\Pr\!\left[
\|A(I-ZZ^T)\|_2
\le (1+\varepsilon)
\min_{\substack{U\in\mathbb R^{n\times k}\\U^TU=I_k}}
\|A(I-UU^T)\|_2
\right]\ge\frac{99}{100}.
```

Probability is over the algorithm's internal randomness, and $`\|\cdot\|_2`$ is the spectral norm.

**Open problem.** Determine $`q_{\mathrm{sp}}(n,k,\varepsilon)`$ up to universal constant factors, with the dependence on $`k`$, $`n`$, and $`\varepsilon`$ simultaneous. In particular, determine the optimal dependence on a growing target rank rather than keeping $`k`$ fixed. The answer must cover the finite-dimensional regime, where learning all columns uses $`n`$ queries.  
This is a square-matrix formulation of the source's question with an editorially fixed two-sided oracle model. The introduction describes products $`Av`$; Algorithm 7.4 explicitly uses both $`A`$ and $`A^T`$. On symmetric inputs these models coincide.

## Why it matters in numerical linear algebra

Matrix products dominate many large-scale singular-subspace computations. The question asks which dependence on the requested number of singular vectors is unavoidable for every adaptive algorithm, rather than for a chosen Krylov implementation.

## References

1. Ainesh Bakshi and Shyam Narayanan, [*Krylov Methods are (nearly) Optimal for Low-Rank Approximation*](https://arxiv.org/html/2304.03191v1#S1.SS2), arXiv:2304.03191v1 (2023), Open Question 1.10; Theorem 1.1 and Algorithm 7.4.
2. Tyler Chen et al., [*Does block size matter in randomized block Krylov low-rank approximation?*](https://arxiv.org/abs/2508.06486), 2025, §1: later block-size bounds.
3. H. Zhang, W. Wu, C. Zhang, Y. Li, C. Zheng, C. Fang, H. Li, and Z. Lin, [*Matrix-Vector Complexity of Low-Rank Approximation*](https://arxiv.org/abs/2609.35840), arXiv:2609.35840, 24 September 2026, abstract; the present literature notice is limited to that primary abstract.

## Status check

The source's $`O(k\log n/\sqrt\varepsilon)`$ upper bound and fixed-rank lower bound do not determine the growing-rank dependence. The 2025 paper studies Krylov block sizes; its clustered-gap conjecture is separately cataloged.

On 2026-09-08 the [source record](https://arxiv.org/abs/2304.03191) still listed only v1. Searches for “Open Question 1.10,” target-rank matrix-vector complexity, and 2025/2026 follow-ups found no joint characterization. The source's lower bound has a sufficiently-large-dimension regime, not every finite $`n,\varepsilon`$. This is a bounded check.

## Audit — 2026-09-10

Rechecked [Bakshi–Narayanan, Theorem 1.1 and Open Question 1.10](https://arxiv.org/html/2304.03191v1). Fixed-rank spectral complexity is settled in the theorem's sufficiently-large-dimension regime; growing-rank and simultaneous finite-parameter dependence remain unresolved. Later query-complexity searches and the [SODA 2026 block-size paper](https://doi.org/10.1137/1.9781611978971.42) did not settle the full target.

## Earlier partial results — 12 September 2026

Holden's [first report](../../references/holden-ra14-2026-09-12/package/report.pdf), Theorems 1.1, 1.2 and 5.1, established the universal rank lower bound, the large-rank regime and a charged spectral-to-PCA reduction yielding matching bounds under a polynomial dimension hypothesis. Its [independent review](../../references/holden-ra14-2026-09-12/independent-review.md) and [submission record](../../references/holden-ra14-2026-09-12/README.md) are retained. The finite-accuracy result below strengthens the lower bound while the full joint characterization remains open.

## Finite-accuracy partial result — 13 September 2026

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. [Submission and verified affiliation](../../references/holden-ra14-v5-2026-09-13/README.md).

[Theorem 1.1](../../references/holden-ra14-v5-2026-09-13/report.pdf) establishes, for a universal positive constant $`c`$ and every original admissible parameter triple,

```math
q_{\mathrm{sp}}(n,k,\varepsilon)\ge c\frac{k}{\sqrt{\varepsilon}}\log\left(1+\frac{n\sqrt{\varepsilon}}{k}\right).
```

Together with the reproduced upper bound, this gives matching universal-factor bounds when $`\varepsilon\le(k/n)^2`$ and when $`\varepsilon\ge k/n`$, including $`q_{\mathrm{sp}}(n,1,1/n)=\Theta(\sqrt n\log n)`$ for $`n>2`$. Sections 3–10 prove the new lower bound; Appendices A and B reproduce the charged reduction and upper bound. [Proof source](../../references/holden-ra14-v5-2026-09-13/report.tex).

The stated partial result passed a separate [independent informal Codex AI-agent audit](../../references/holden-ra14-v5-2026-09-13/independent-review.md). **RA-14 remains Partially resolved:** at $`k=1`$ and $`\varepsilon=(\log n/n)^2`$, the bounds still leave $`\Omega(n\log\log n/\log n)`$ versus $`O(n)`$, an unbounded factor. The full simultaneous universal-factor target is unchanged. No Lean verification, external human peer review or priority claim is asserted. This continues the earlier partial submission [PR #190](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/190); it does not duplicate a previously pushed full solution.


## Restricted Krylov and posterior continuation — 13 September 2026

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. [Submission and verified affiliation](../../references/holden-ra14-v6-2026-09-13/README.md).

[Theorem 2.2](../../references/holden-ra14-v6-2026-09-13/report.pdf) characterizes the deterministic-width, fully charged block span-query class of Definition 2.1, with no fresh directions or within-round adaptation, but arbitrary outputs:

```math
q_{\mathrm{fb}}(n,k,\varepsilon)=\Theta\!\left(\min\left\{n,\frac{k}{\sqrt\varepsilon}\log\frac{en}{k}\right\}\right).
```

The constants are universal and the statement covers all original finite parameters **inside this restricted class**. Theorem 10.1 gives an adaptive shifted singular-Wishart posterior only on its stated domain. Theorem 11.2 gives a rank-one upper bound averaged over that particular input law and the Gaussian start; it is not a pointwise guarantee for every matrix. [Proof source](../../references/holden-ra14-v6-2026-09-13/report.tex).

These new partial scopes passed a separate [independent informal Codex AI-agent review](../../references/holden-ra14-v6-2026-09-13/independent-review.md). **RA-14 remains Partially resolved.** This continuation does not improve the unrestricted bounds above, and the same finite-accuracy transition gap remains. No Lean verification or external human peer review is asserted. Earlier partial submissions [#190](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/190) and [#220](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/220) remain credited; this is not a duplicate of a previously pushed full solution.
