# MI-07 — The triangle conjecture for the maximal symmetric modulus

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Lean verified

**Last checked:** 2026-09-12

**Rating rationale:** Combining spectral-order suprema with ordinary matrix-order domination requires new analysis; the immediate audience is operator-inequality specialists.

## Lean proof and verification evidence — 2026-09-12

**The original constant-one MI-07 conjecture is false, with a complete Lean-verified counterexample.** At the fixed rational pair

```math
A=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
B=\begin{pmatrix}0&5/12\\0&0\end{pmatrix},
```

the actual maximal moduli are $`M(A)=A`$, $`M(B)=(5/12)I`$ and $`M(A+B)=(13/12)I`$. The left trace is $`13/6`$, whereas every complex unitary pair gives right trace $`11/6`$. The right-minus-left trace is $`-1/3`$, which excludes ordinary PSD domination. The [proof at revision f557771](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/f55777156432043de4201747a3759e0c6485e568/matrix-inequalities-and-norms/MI-07/lean) retains the full original complex-matrix and unitary quantifiers and proves the actual root-sequence limits at all three counterexample arguments.

**Mathematical counterexample and informal proof:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance.

The seven checked declarations in [Solution.lean](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/f55777156432043de4201747a3759e0c6485e568/matrix-inequalities-and-norms/MI-07/lean/Solution.lean) are:

- `NLA.MI07.modulus_eq_sqrt`: the genuine positive square-root modulus.
- `NLA.MI07.maximalModulus_eq_of_tendsto`: identification of the actual limit from proved convergence.
- `NLA.MI07.root_limit_iff_spectralNorm`: equivalence with convergence in the genuine Euclidean operator norm.
- `NLA.MI07.witness_moduli`: all exact polar factors and positivity facts.
- `NLA.MI07.witness_root_limits`: the three actual root-sequence limits.
- `NLA.MI07.counterexample`: the exact all-unitary trace obstruction.
- `NLA.MI07.not_triangleConjecture`: negation of the complete original universal assertion.

Two independent agents reviewed the [frozen statements and completed proof](lean/reviews/). [Linux run 34709291624](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34709291624) matched all seven exports with the sandboxed Comparator and replayed them through Lean's default kernel. The [original artifacts and operational audit](lean/verification/linux-2026-09-12/) retain source hashes, isolation checks and rejection controls. The [transitive axiom reports](lean/reviews/proof-axioms.log) contain only `propext`, `Classical.choice` and `Quot.sound`. These are independent agent reviews, not external human peer review.

The proof pins **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). See the [manifest](lean/formalization.yaml), [dependency pins](lean/lake-manifest.json) and [numerical targets](lean/NUMERICAL_TARGETS.md). On a documented [non-root Linux host](../../tools/lean/HARNESS.md), reproduce from the verified revision with:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  matrix-inequalities-and-norms/MI-07/lean \
  /absolute/path/to/nla-lean-tools
```

The manuscript's stronger no-finite-constant theorem and generic convergence for unrelated matrices are outside these seven exports. The original informal proof and its historical audit remain below.

## Resolution — 2026-09-11

**Negative result by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent proof review: PASS.**

No finite two-unitary domination constant exists for the maximal symmetric modulus, already in dimension two. The rank-one family gives the necessary bound $`C\ge\sqrt{1+t^2}/t`$ for every $`t>0`$.

The exact target is resolved. The original statement and source evidence are retained below; its former difficulty rating is historical.

**Primary manuscript:** [complete proof PDF](solution.pdf), [standalone TeX](solution.tex), Theorem 1.1 and its proof; [authorship and scope](solution.md). The [independent review](../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-07-review.md) checks the full original argument and records its hash. The draft was AI-assisted; the 2026-09-11 review was independent agent verification, without external human peer review or formal certification. The later Lean verification above covers the complete original constant-one target. [Submission record](../../references/colbrook-matrix-2026-09-11/README.md).

## Problem statement

For a complex square matrix $`X`$, let $`|X|=(X^*X)^{1/2}`$ and define its maximal symmetric modulus by the finite-dimensional limit

```math
M(X)=\lim_{r\to\infty}\bigl(|X|^r+|X^*|^r\bigr)^{1/r},\qquad r\in\mathbb N.
```

This is the supremum of $`|X|`$ and $`|X^*|`$ in Olson's spectral order. For every $`n\ge1`$ and every $`A,B\in\mathbb C^{n\times n}`$, must there exist unitary $`U,V`$ of order $`n`$ satisfying

```math
M(A+B)\preceq U M(A)U^*+V M(B)V^*?
```

The order in this displayed inequality is ordinary positive-semidefinite order.

## Why it matters

The modulus combines both positive polar factors through spectral order. A sharp triangle inequality would give a new way to control positive representatives of nonnormal matrix sums.

## References

1. J.-C. Bourin and E.-Y. Lee, *Averages over matrix unitary orbits and spectral order*, arXiv:2606.15624v2 (18 June 2026), §§3.1–3.3, Question 3.11 and Conjecture 3.12. [Primary text](https://arxiv.org/html/2606.15624).
2. J.-C. Bourin and E.-Y. Lee, *Some hybrid matrix triangle inequalities*, arXiv:2606.29188v1 (28 June 2026), §3, Lemma 3.3 and Theorem 3.4. [Primary text](https://arxiv.org/html/2606.29188).

## Status check — 2026-09-10

Latest versions v2 and v1 were checked. The follow-up proves inequalities with the ordinary modulus of the total sum on the left, while the present conjecture has its maximal symmetric modulus there. Its conclusion therefore does not establish the displayed assertion. Searches included `maximal symmetric modulus conjecture`, `Bourin Lee 2606.15624 conjecture`, and `Some hybrid matrix triangle inequalities`. No later resolution was located.

**Audit update (2026-09-10):** Rechecked Bourin–Lee Conjecture 3.12 and their hybrid follow-up, then searched for maximal-modulus triangle results. The follow-up does not replace its left-hand ordinary modulus by the maximal modulus required here. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
