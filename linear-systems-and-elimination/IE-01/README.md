# IE-01 — Forsythe's conjecture beyond restart length two

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** Lean verified  
**Last checked:** 2026-09-11  

> **LEAN VERIFIED — complete classification.** The conjecture holds for restart length three and fails for every restart length at least four. The paper and its public Lean verification record settle the entire original target. This retained entry is excluded from the open count.

**Rating rationale:** Historical ratings describe the original long-standing convergence problem and its importance for iterative linear solvers. They are not an estimate of remaining work after the resolution.

## Original problem statement

Let $A\in\mathbb R^{n\times n}$ be symmetric positive definite, $b,x_0\in\mathbb R^n$, and $3\leq s<n$. At each restart, perform exactly $s$ exact-arithmetic conjugate-gradient steps, starting from the last iterate, and discard the previous search directions. Denote the iterate after restart cycle $j$ by $x_j$. Suppose this process never terminates exactly, and put

$$
r_j=b-Ax_j,\qquad y_j=r_j/\|r_j\|_2.
$$

Prove or disprove that both $(y_{2j})_{j\geq0}$ and $(y_{2j+1})_{j\geq0}$ converge in $\mathbb R^n$, for every such input and restart length. The question concerns directions, not whether the residual norms tend to zero. Exact termination is excluded so every normalization exists.

## References

Faber, Liesen, and Tichý, [*On the Forsythe conjecture*](https://doi.org/10.1007/s10543-023-00991-x), BIT 63 (2023), §2, especially the displayed Forsythe conjecture. Colbrook, Stepaniants, and Townsend, [*A Proof of the Forsythe Conjecture for the Two-Step Restarted Conjugate Gradient Method*](https://arxiv.org/abs/2608.02852), August 2026, §1 and main theorem.

## Resolution and status check — 2026-09-11

M. J. Colbrook, G. Stepaniants, and A. Townsend, *A Complete Resolution of Forsythe's Conjecture for Restarted Conjugate Gradients*, [arXiv:2609.04659v2](https://arxiv.org/abs/2609.04659v2), submitted September 4 and revised September 7, 2026, **Theorem 1.1**.

Theorem 1.1 proves termination or separate convergence of the even and odd normalized residuals for $s=2,3$. For each $s\ge4$, it constructs a diagonal positive definite matrix of dimension exactly $s+4$ and a nonterminating iteration whose even normalized residuals do not converge. Thus the original target is affirmative at $s=3$ and negative at every $s\ge4$, with no remaining cases. The real SPD, exact-arithmetic and residual-normalization conventions match the original statement, and the counterexamples satisfy $s<n$. Together with Akaike's classical $s=1$ theorem, this gives the sharp threshold $s\in\{1,2,3\}$.

## Lean proof and verification evidence

[Appendix D](https://arxiv.org/html/2609.04659v2) documents the formal proof in the authors' [Forsythe repository](https://github.com/sgstepaniants/Forsythe/tree/main/lean-proof). The entry point [Solution.lean](https://github.com/sgstepaniants/Forsythe/blob/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof/Solution.lean) exports `forsytheSharpClassification`, including both positive cases and the diagonal counterexamples. [Definitions.lean](https://github.com/sgstepaniants/Forsythe/blob/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof/ProofProject/Definitions.lean) specifies affine-Krylov energy minimization, termination and signed Euclidean residual directions. The proof covers the analytic construction of exact trajectories and establishes its numerical premises within Lean.

The public [verification record](https://github.com/sgstepaniants/Forsythe/blob/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof/VERIFICATION.md) and [full Comparator transcript](https://github.com/sgstepaniants/Forsythe/blob/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof/verification-logs/linux-comparator-final.log) record successful statement comparison and kernel replay for all five exported declarations on September 5, 2026, using only `propext`, `Classical.choice` and `Quot.sound`. The record also documents the September 6 source cleanup and subsequent type/axiom checks. The formalization does not separately prove Akaike's $s=1$ theorem or the particular parameter specification in Proposition C.1.2; neither is required for IE-01.

The pinned [reproduction guide](https://github.com/sgstepaniants/Forsythe/blob/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof/reproduction/README.md) provides the build and Comparator replay commands. The [toolchain file](https://github.com/sgstepaniants/Forsythe/blob/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof/lean-toolchain) selects Lean 4.33.1, and the [dependency manifest](https://github.com/sgstepaniants/Forsythe/blob/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof/lake-manifest.json) pins the library revisions. The complete target is exported as `ProofProject.forsytheSharpClassification`; its statement and transitive axiom checks are included in the linked transcript.

**Verification level:** Lean verified, based on reviewed public verification evidence. The inspected source revision is [8d1b0c0](https://github.com/sgstepaniants/Forsythe/tree/8d1b0c0545a77b40245e84705aa7d273e6c81e62), dated September 7, 2026. On September 11, this catalog checked Theorem 1.1, Appendix D, the formal statement/definition correspondence and the published verification record. The Lean build and Comparator replay were not rerun locally. The former **Solution claimed** and **Solved** labels are superseded by the explicit formal-verification level. IE-01 was excluded from the open count on September 8; its original ID, path, statement and historical ratings remain intact.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Solved and claimed solutions](../../RESOLVED.md#ie-01) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
