# KE-03 — Find a near-largest nonnormal eigenvalue using few matrix-vector products

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Topic:** nonsymmetric eigenvalue computation; query complexity  
**Last checked:** 2026-09-11  
**Status:** Solved  

**Rating rationale:** Challenging reflects a query bound for general nonnormal matrices, whose eigenvalues need not be controlled by power iteration; community impact is the complexity of large nonsymmetric eigenproblems.

## Resolution — 2026-09-11

**Affirmative resolution by Matthew J. Colbrook** (Department of Applied Mathematics and Theoretical Physics, University of Cambridge). See the [complete manuscript](solution.md), **Theorem KE-03, sections 1–5** ([PDF](solution.pdf) · [LaTeX](solution.tex)), prepared 11 September 2026.

The algorithm uses $`O(\varepsilon^{-2}[1+\log(nK)])`$ exact matrix-vector queries, with success probability at least $`0.997`$, for every input in the displayed model. It supplies both eigenvalue-location guarantees using the given condition bound $`K`$ and finite exact arithmetic between queries. The result bounds query count, not total runtime, bit complexity or floating-point error.

The original proof draft was generated in a ChatGPT conversation. A separate Codex agent independently verified the full proof and its match to the exact target on 11 September 2026: [detailed PASS review](../../references/colbrook-2026-09-11/verification/reviews/KE-03-review.md). The review records a hash of the unchanged proof text. This is independent agent verification, not external human peer review or formal certification. [The submission history and diagnostic record](../../references/colbrook-2026-09-11/README.md) preserve the initial solution claim. The ratings above are historical, and the earlier literature checks below are retained.

## Context and notation

All norms are Euclidean vector norms or their induced matrix norms.

## Problem statement

An unknown diagonalizable $`A\in\mathbb C^{n\times n}`$ is available only
through exact queries $`v\mapsto Av`$. A number $`K\geq1`$ is supplied, with
the promise that $`A=V\Lambda V^{-1}`$ for some diagonal $`\Lambda`$ and
$`\|V\|_2\|V^{-1}\|_2\leq K`$. Assume
$`\rho(A)=\max_{\mu\in\sigma(A)}|\mu|>0`$; neither the eigenvalues nor $`V`$
are supplied.

Do universal constants $`C,a,b>0`$ and a randomized algorithm exist that,
for every such input and every $`\varepsilon\in(0,1/2)`$, returns a complex
number $`z`$ with probability at least $`0.99`$ such that

```math
\text{there exists }\mu\in\sigma(A):
\quad |\mu|\geq(1-\varepsilon)\rho(A),
\qquad |z-\mu|\leq\varepsilon\rho(A),
```

using at most $`C[1+\log(nK)]^a\varepsilon^{-b}`$ matrix-vector queries?
The algorithm may perform finite exact arithmetic between queries; the
requested bound concerns query count. Products with $`A^*`$ and solutions of
shifted linear systems are not additional oracle operations. Supplying $`K`$
and fixing a success probability make the computational formulation explicit.

## References

Amsel et al., [workshop report](https://arxiv.org/html/2602.05394v3#S3.SS5),
Problem 3.9. Shah, Srivastava, and Zeng,
[*Sparse Pseudospectral Shattering*, first version](https://arxiv.org/pdf/2411.19926v1),
§1.3, Theorem 1.5 and its power-iteration argument, supplies the related
spectral-radius estimate cited by the workshop.

## Earlier status check — 2026-09-08

Searches for `nonnormal eigenvalue query complexity 2026`
and `nonnormal spectral radius matrix-vector algorithm 2026` found no
resolution. The radius estimate controls a nonnegative scalar and allows
backward error; it does not locate a near-extremal eigenvalue in the complex
plane as required here. The [April 2026 third version](https://arxiv.org/abs/2411.19926v3)
replaces that application with a GMRES application (§6), so the version-specific
locator above is intentional. The workshop still poses Problem 3.9 in its
August update, separately from its resolved general Ritz-compression question.

## Audit update — 2026-09-10

Rechecked [workshop version 3](https://arxiv.org/html/2602.05394v3), Problem 3.9. Searches for nonnormal largest-eigenvalue matrix-vector query bounds found no theorem or lower bound settling the displayed question. Hermitian or singular-value oracle results do not answer it.
