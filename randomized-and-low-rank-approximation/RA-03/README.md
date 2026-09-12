# RA-03 — Improve the randomized LU squared-error factor to $`2^k`$

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Rating rationale:** Challenging because nonsymmetric residuals lose the trace identities behind Cholesky bounds; specialist impact is a sharper guarantee for one randomized LU rule.  
**Topic:** randomized LU; low-rank approximation  
**Last checked:** 2026-09-12

**Status:** Lean verified

## Lean proof and verification evidence — 2026-09-12

**The original RA-03 conjecture is false, with a complete Lean-verified counterexample.** The [proof at revision 973f959](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/973f95969701601dcae7b30683b175843baa9c22/randomized-and-low-rank-approximation/RA-03/lean) proves that $`A=\left(\begin{smallmatrix}2&1\\1&2\end{smallmatrix}\right)`$ has expected squared Frobenius residual $`18/5>2`$ after one pivot, whereas its actual rank-one singular-value tail is $`1`$. The formal statement retains arbitrary complex rectangular inputs, the joint conditional entry probabilities, zero absorption, the genuine Frobenius norm and all admissible ranks. Its exact witness refutes the full original universal bound.

**Mathematical counterexample and informal proof:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance.

The checked declarations in [Solution.lean](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/973f95969701601dcae7b30683b175843baa9c22/randomized-and-low-rank-approximation/RA-03/lean/Solution.lean) are:

- `NLA.RA03.frobeniusSq_eq_norm_sq`: the actual squared Frobenius norm.
- `NLA.RA03.process_isProbability`: normalization of every conditional law and complete-history law.
- `NLA.RA03.counterexample`: the exact witness, ordered singular values, four pivot updates and strict violation.
- `NLA.RA03.not_squaredErrorConjecture`: negation of the complete original conjecture.

Two independent agents [reviewed the frozen statements and complete proof](lean/reviews/) against the original target. [Run 34704564047](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34704564047) executed the real sandboxed Comparator on GitHub Actions Ubuntu 24.04, matched all four declarations and replayed the solution through Lean's default kernel. The [archived logs and independent operational audit](lean/verification/linux-2026-09-12/) retain the exact source hashes, original artifact digests and actual rejection controls for `sorry` and native-execution axioms. The [transitive axiom log](lean/reviews/proof-referee-2-evidence/axioms.log) contains only `propext`, `Classical.choice` and `Quot.sound`. The operational audit inspected the downloaded Linux evidence locally on macOS; it did not rerun Linux locally. These are independent agent reviews, not external human peer review.

The proof pins **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). The [manifest](lean/formalization.yaml), [dependency pins](lean/lake-manifest.json) and [numerical targets](lean/NUMERICAL_TARGETS.md) record the scope and implementation. From a checkout of the verified revision, with the documented [non-root Linux prerequisites](../../tools/lean/HARNESS.md), reproduce the check with:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  randomized-and-low-rank-approximation/RA-03/lean \
  /absolute/path/to/nla-lean-tools
```

The shared manuscript's stronger sharp all-rank $`4^r`$ result and its Cholesky results remain separately informally reviewed; they are outside these four Lean exports.

<!-- colbrook-random-pivoting -->
## Resolution — 2026-09-11

**Negative resolution by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Section 2 gives the exact counterexample $`A=\left(\begin{smallmatrix}2&1\\1&2\end{smallmatrix}\right)`$: one pivot has expected squared Frobenius error $`18/5`$, while the best rank-one squared error is $`1`$. Thus the displayed $`2^k`$ bound is false already at $`k=1`$. Theorem 1 additionally proves that the known $`4^r`$ factor is sharp as a supremum at every rank, even on real entrywise-positive positive-definite inputs.

[Complete manuscript](../../references/colbrook-random-pivoting-2026-09-11/manuscripts/sharp_random_pivoting.pdf) · [TeX](../../references/colbrook-random-pivoting-2026-09-11/manuscripts/sharp_random_pivoting.tex) · [Independent complete-source PASS review](../../references/colbrook-random-pivoting-2026-09-11/verification/reviews/RA-03-review.md) · [Authorship, exact checks and provenance](../../references/colbrook-random-pivoting-2026-09-11/README.md).

The 2026-09-11 verification was independent agent review, without external human peer review or formal certification. The later Lean verification above covers the complete negative answer to the original conjecture. AI assistance is disclosed; no priority claim is made. The original statement and audits remain below; ratings are historical.
<!-- /colbrook-random-pivoting -->

## Problem statement

For $`A\in\mathbb C^{m\times n}`$, define exact-arithmetic residuals
$`S_0=A`$. At step $`t`$, choose $`(i,j)`$ with conditional probability
$`|(S_t)_{ij}|^2/\|S_t\|_F^2`$ and update

```math
S_{t+1}=S_t-\frac{S_t(:,j)S_t(i,:)}{(S_t)_{ij}}.
```

After a zero residual, keep subsequent residuals zero. Prove or refute,
for every $`m,n\geq1`$, every $`A`$, and every
$`1\leq k\leq\min(m,n)`$,

```math
\mathbb E\|S_k\|_F^2\leq2^k
\sum_{j>k}\sigma_j(A)^2,
```

where singular values decrease with $`j`$. The bound concerns the mean
squared Frobenius error of this specified algorithm.

## References

Gilles and Wilber, [*Low-Rank Approximation by Randomly
Pivoted LU*](https://arxiv.org/html/2601.22344v1), Algorithm 1 and §3.1,
Theorem 3, Eq. (10), and the following conjecture (pp. 7–8).

## Status check

Their theorem gives $`4^k`$; the conjecture explicitly
replaces it by $`2^k`$. Searches for the title, `randomly pivoted LU 2^k`,
and improved RPLU error bounds found no later resolution. The arXiv
submission history listed only v1 of January 29, 2026. The August 2026
RPCholesky theorem addresses a different pivot distribution and norm.

## Audit — 2026-09-10

Rechecked [Algorithm 1, Theorem 3, and the following conjecture](https://arxiv.org/html/2601.22344v1); its record still lists v1. RPLU and improved-bound searches found no resolution. The theorem remains at $`4^k`$, while the stated squared-error conjecture is $`2^k`$.
