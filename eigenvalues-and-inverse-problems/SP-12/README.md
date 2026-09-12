# SP-12 — A chromatic lower bound for positive-semidefinite nullity with SAP

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Solved
**Last checked:** 2026-09-11

**Rating rationale (historical):** Challenging reflects the need for a stronger general PSD/SAP realization bound than current connectivity estimates supply; implication from Hadwiger does not establish equivalent difficulty. Specialist impact reflects the focus on this particular graph nullity invariant.

## Literature-dependent resolution - 2026-09-11

**Solved.** Hall's **Corollary 3.22**, based on **Theorem 3.20**, gives $\nu(H)\ge\delta(H)$ for every graph $H$. Induced-subgraph monotonicity and a vertex-critical subgraph of chromatic number $\chi(G)$ then prove the exact target $\nu(G)\ge\chi(G)-1$. The application note supplies the complete monotonicity and coloring argument, including rank-zero and disconnected cases.

The all-graph theorem is due to **H. Tracy Hall**, [*The Delta Theorem*, arXiv:2601.01211v1](https://arxiv.org/html/2601.01211v1), submitted 3 January 2026. **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, is the author of the [explanatory application note](solution.md); no new theorem discovery or priority is claimed. [Application PDF](solution.pdf) · [Standalone TeX](solution.tex).

A separate [Codex-agent review](../../references/stepaniants-sp11-sp12-2026-09-11/verification/SP-11-SP-12-independent-review.md) checked the full essential proof in Hall's preprint and the exact deduction and returned **PASS**. The source remains a preprint; this is independent automated-agent review, not external human peer review or formal verification. Substantial ChatGPT/Codex assistance and the review's precise limits are disclosed in the [submission record](../../references/stepaniants-sp11-sp12-2026-09-11/README.md).

The earlier status checks below are retained as historical records. The original ID, target, path, historical ratings and attributed partial results remain unchanged. Unsupported prior artifact and graph-atlas claims remain withdrawn.

## Problem statement

Let $G$ be a finite simple undirected graph on $n\ge1$ vertices. Let $\mathcal S(G)$ be the real symmetric matrices whose off-diagonal nonzero entries occur exactly at edges of $G$, with unrestricted diagonal.

A matrix $A\in\mathcal S(G)$ has the **strong Arnold property (SAP)** if the only real symmetric matrix $X$ satisfying
$$
AX=0,\qquad A\circ X=0,\qquad I_n\circ X=0
$$
is $X=0$, where $\circ$ is the entrywise product. Define
$$
\nu(G)=\max\{\dim\ker A:A\in\mathcal S(G),\ A\succeq0,\ A\text{ has SAP}\}.
$$
Writing $\chi(G)$ for the minimum number of colors in a proper vertex coloring, does every $G$ satisfy
$$
\nu(G)\ge\chi(G)-1?
$$

## Relevance and ratings

 The conclusion asserts the existence of a positive-semidefinite matrix, with an exact prescribed sparsity pattern, of rank at most $n-\chi(G)+1$ and with an additional nondegeneracy property. Equivalently it constrains structured Gram matrix construction. This is adjacent to core NLA through matrix realization and inverse eigenvalue theory.

## References

- F. Barioli, S. M. Fallat, H. Gupta, and Z. Li, *The weak version of the graph complement conjecture and partial results for the delta conjecture*, Discrete Mathematics 349 (2026), 114861, Conjecture 4.1 and §1 definitions ([primary manuscript](https://arxiv.org/html/2505.24577v1); [journal](https://doi.org/10.1016/j.disc.2025.114861)).
- F. Barioli, S. M. Fallat, and L. Hogben, *A variant on the graph parameters of Colin de Verdière: Implications to the minimum rank of graphs*, Electronic Journal of Linear Algebra 13 (2005), 387–404, pp.388–390 on SAP and nullity parameters ([primary paper](https://journals.uwyo.edu/index.php/ela/article/download/341/341)).

- M. Chudnovsky and A. Ovetsky Fradkin, *Hadwiger's conjecture for quasi-line graphs*, Journal of Graph Theory 59 (2008), 17–33, Theorem 1.1 ([primary manuscript](https://web.math.princeton.edu/~mchudnov/Hadwiger_quasiline.pdf); [journal](https://doi.org/10.1002/jgt.20321)).

## Status check

 This exact inequality is expressly proposed in the 2026 paper. Its weaker independence-number consequence, Conjecture 4.4, is not separately counted. The source explains that the strong delta conjecture and Hadwiger's conjecture would each imply the assertion; the original unrestricted symmetric delta conjecture in the companion entry is a different statement. Searches for this paper, “nu”, “chromatic”, “positive semidefinite”, “conjecture”, and 2026 found no resolution. No claim is made that these conjectures are logically independent.

The 2026 counterexamples to a Colin de Verdière conjecture about Laplace eigenvalue multiplicities on surfaces concern a different invariant; they do not refute this finite PSD/SAP inequality.

## Audit update — 2026-09-10

**Partially resolved:** the inequality holds for quasi-line graphs, meaning each vertex neighborhood is the union of two cliques. This follows by combining Chudnovsky–Fradkin Theorem 1.1 with the proved inequality $\nu(G)\ge\eta(G)-1$ recalled immediately before Conjecture 4.1, where $\eta$ is the largest clique-minor order. This is an implication of two established results, not a claim that the general conjecture is proved. Both full primary texts, the 2026 publication record, and targeted later searches were checked; no general resolution was located.
