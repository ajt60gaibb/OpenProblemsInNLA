# MI-23 — Corrected generalized geometric-mean product conjecture

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Lean verified
**Last checked:** 2026-09-12

**Rating rationale:** The four interacting exponents make this corrected conjecture challenging; its immediate consequences concern specialists in matrix means and log-majorization.

## Lean proof and verification evidence - 2026-09-12

**The complete corrected MI-23 conjecture is false, with a Lean-verified counterexample.** The rational complex positive-definite witness has $`r=s=1`$, $`p=2`$, $`t=1/8`$ and violates the first ordered eigenvalue inequality. The [proof at revision 17194f9](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/17194f9060609acae429e14d3dc3c4562b84f2bd/matrix-inequalities-and-norms/MI-23/lean) preserves every original dimension, both real $`r,s`$ regions, actual CFC matrix powers, all proper prefix products and equality of complete products.

**Mathematical counterexample and informal proof:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance.

The eight [checked exports](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/17194f9060609acae429e14d3dc3c4562b84f2bd/matrix-inequalities-and-norms/MI-23/lean/Solution.lean), each with prefix `NLA.MI23.`, are:

- `positive_powers_and_means`: genuine CFC powers and generalized means are positive definite.
- `product_eigenvalue_semantics`: complete characteristic roots with multiplicities, positivity, ordering, similarity and determinant product.
- `squared_product_largest`: the actual largest root of $`X^2Y^2`$ equals $`\|XY\|_2^2`$.
- `operator_norm_bounds`: entry and Frobenius bounds for the genuine Euclidean operator norm.
- `witness_data`: admissibility and all actual CFC witness identities.
- `witness_squared_gap`: the exact rational gap and strict operator-norm separation.
- `counterexample`: failure of the original log-majorization relation at the admissible witness.
- `not_generalizedGeometricMeanConjecture`: negation of the complete universal conjecture.

Two independent agents reviewed the [frozen statements and completed proof](lean/reviews/). [Linux run 34716784038](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34716784038) matched all eight exports using the sandboxed Comparator and replayed the solution in Lean's default kernel. The [original artifacts and independent operational audit](lean/verification/linux-2026-09-12/) bind all 133 verified source inputs and both actual isolation and rejection-control suites. All 64 [internal/public transitive axiom reports](lean/verification/linux-2026-09-12/axiom-verification.json) contain only `propext`, `Classical.choice` and `Quot.sound`. These are independent agent reviews, without a claim of external human peer review.

The proof pins **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). Exact integer-power identities replace fractional-power approximation. One kernel-mode LeanCert certificate proves the positive rational gap and remains in the final norm and eigenvalue contradiction. See the [manifest](lean/formalization.yaml), [dependency pins](lean/lake-manifest.json) and [numerical targets](lean/NUMERICAL_TARGETS.md). From the verified revision on a documented [non-root Linux host](../../tools/lean/HARNESS.md), reproduce with:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  matrix-inequalities-and-norms/MI-23/lean \
  /absolute/path/to/nla-lean-tools
```

This settles the corrected eigenvalue conjecture stated below. The earlier singular-value conjecture is a different target. The original problem and historical informal proof remain intact.

## Resolution — 2026-09-11

**Negative result by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent proof review: PASS.**

Rational positive definite $`3\times3`$ matrices with $`r=s=1`$, $`p=2`$ and $`t=1/8`$ violate the corrected eigenvalue log-majorization conjecture. An exact integer-power construction and rational norm separation establish failure of the first ordered eigenvalue inequality.

The exact target is resolved. The original statement and source evidence are retained below; its former difficulty rating is historical.

**Primary manuscript:** [complete proof PDF](solution.pdf), [standalone TeX](solution.tex), Theorem 1.1 and its proof; [authorship and scope](solution.md). The [independent review](../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-23-review.md) checks the full original argument and records its hash. The draft was AI-assisted; the 2026-09-11 review was independent agent verification, without external human peer review or formal certification. The later Lean verification above covers the complete corrected target. [Submission record](../../references/colbrook-matrix-2026-09-11/README.md).

## Problem statement

For positive definite $`A,B\in\mathbb C^{n\times n}`$, real $`r`$, and $`t\in[0,1]`$, define

```math
G_{r,t}(A,B)=A^{r/2}(A^{-1/2}BA^{-1/2})^tA^{r/2}.
```

Is it true, for every $`n\ge1`$, every such $`A,B`$, every $`p\ge1`$, $`t\in[0,1]`$, and either $`r,s\ge1`$ or $`r,s\le0`$, that

```math
\lambda\bigl(G_{r,t}(A,B)^pG_{s,1-t}(A,B)^p\bigr)
\prec_{\log}\lambda\bigl(A^{p(r+s-1)}B^p\bigr)?
```

The eigenvalues of these products are positive real numbers, ordered decreasingly: each product is similar to a positive definite matrix. For positive decreasing vectors $`x,y\in\mathbb R^n`$, $`x\prec_{\log}y`$ means $`\prod_{j=1}^kx_j\le\prod_{j=1}^ky_j`$ for $`1\le k< n`$, with equality at $`k=n`$.

This compares nonlinear matrix-mean products with products of powers of the input matrices. It would give simultaneous multiplicative control for every partial product of ordered eigenvalues and strengthen norm estimates used with positive definite matrix functions.

## References

1. M. M. Ghabries, H. Abbas, B. Mourad and A. Assi, *New log-majorization results concerning eigenvalues and singular values and a complement of a norm inequality*, preprint (2021), Conjecture 2.1, p. 6. [PDF](https://arxiv.org/pdf/2105.13356).
2. M. M. Ghabries, *Contributions to Matrix Inequalities and Some Applications*, PhD thesis, University of Angers and Lebanese University (2022), final Open Problems, Problem 6, pp. 109–110. [Thesis uploaded by its author](https://www.researchgate.net/publication/361793582_Contributions_to_Matrix_Inequalities_and_Some_Applications).
3. M. M. Ghabries, *A log-majorization inequality for normal matrices with applications to determinantal inequalities and geometric means* (2026), §4. [Full text](https://arxiv.org/html/2607.21163).

Status check (2026-09-10): Theorem 2.1 and equation (13) of the first source prove a substantive included region: $`r,s\ge1`$, $`1\le p\le2`$, and $`\frac{r(p-1)}{(r+s)p}\le t\le\frac{rp+s}{(r+s)p}`$. This includes $`p=1`$ for all $`t`$. The full parameter range is the remaining question. The first source refutes its earlier unrestricted singular-value Conjecture 1.2; the statement here is the explicitly proposed replacement. The thesis retains it. The July 2026 paper concerns eigenvalue products of ordinary weighted means and does not claim this full $`r,s,p`$ statement. Current arXiv versions and searches for the authors, “Conjecture 2.1 generalized geometric mean” and 2025/2026 yielded no full resolution. This is a bounded check, not certification of openness.
