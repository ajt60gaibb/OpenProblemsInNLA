# MI-19 — A q-permanent inequality for subset-preserving permutations

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Lean verified

**Last checked:** 2026-09-12

**Rating rationale:** Arbitrary subsets introduce inversion-order interactions absent for an initial segment; a solution would advance specialized block inequalities for generalized permanents.

## Resolution — 2026-09-11

**Negative result by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent proof review: PASS.**

A real order-four PSD Gram matrix, $q=7/8$ and the interior singleton $S=\{2\}$ give full minus restricted $q$-permanent equal to $-3235575/16384$. Inversions are counted in the full original ordering. The strict counterexample also persists under sufficiently small positive diagonal perturbations.

The exact target is resolved. The original statement and source evidence are retained below; its former difficulty rating is historical.

**Lean verification — 2026-09-12:** the complete negative target passed independent statement and proof reviews, followed by Linux Comparator and kernel checks. [Proof and verification evidence](#lean-proof-and-verification-evidence--2026-09-12).

**Primary manuscript:** [complete proof PDF](solution.pdf), [standalone TeX](solution.tex), Theorem 1.1 and its proof; [authorship and scope](solution.md). The [independent review](../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-19-review.md) checks the full original argument and records its hash. The draft was AI-assisted; that informal audit was independent agent verification, not external human peer review or formal certification. [Submission record](../../references/colbrook-matrix-2026-09-11/README.md).

## Lean proof and verification evidence — 2026-09-12

**Mathematical counterexample:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.

The [Lean proof](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/cd44ce9bcb84ebc79a1aa934918d1f76b2a9c6e7/matrix-inequalities-and-norms/MI-19/lean/NLA/MI19/Proof.lean) and [public declarations](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/cd44ce9bcb84ebc79a1aa934918d1f76b2a9c6e7/matrix-inequalities-and-norms/MI-19/lean/Solution.lean) are fixed at [proof revision cd44ce9](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/cd44ce9bcb84ebc79a1aa934918d1f76b2a9c6e7/matrix-inequalities-and-norms/MI-19/lean). The selected declarations are:

- `NLA.MI19.counterexample`;
- `NLA.MI19.not_subsetConjecture`.

The second theorem negates the complete original statement: every $n\ge2$, every complex Hermitian PSD matrix, every real $q\in[0,1]$, and every nonempty proper subset, with setwise preservation and inversion counts in the full original ordering. All witness hypotheses are proved. The actual complex PSD order-four Gram witness has $q=7/8$ and the interior singleton, giving full minus restricted q-permanent $-3235575/16384$. Exact rank, all-q polynomial identities, and the positive-diagonal-perturbation extension are not among the formalized claims.

The toolchain is Lean 4.33.1, with [LeanCert 621a43d](https://github.com/alerad/leancert/commit/621a43d7cf21f87872392a01e874f2f1dbddc926) and [mathlib 0df444a](https://github.com/leanprover-community/mathlib4/commit/0df444a360eaa60ab8c11dca51a86af692955474); [all dependencies are locked](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/cd44ce9bcb84ebc79a1aa934918d1f76b2a9c6e7/matrix-inequalities-and-norms/MI-19/lean/lake-manifest.json). LeanCert checks one exact scalar inequality in kernel mode. Both public theorems and the five audited internal declarations have only `propext`, `Classical.choice`, and `Quot.sound` in their transitive axiom closure.

The catalog reviewed [successful Linux verification on 12 September 2026](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34703363593/job/103578942995): fresh problem builds, real sandbox isolation controls, exact Challenge/Solution comparison with no definition holes, the standard-three axiom whitelist, and Lean default-kernel replay. The pinned mathlib dependency cache was used. Both requested theorems passed; sorry, custom-axiom, statement-mismatch, invalid-kernel-proof, and native-trust rejection controls also executed successfully. The [operational audit](lean/verification/linux-2026-09-12/OPERATIONAL-REVIEW.md), [Comparator log](lean/verification/linux-2026-09-12/artifacts/lean-MI-19/verify-20260912T155027Z-3941/comparator.log), and [result receipt](lean/verification/linux-2026-09-12/artifacts/lean-MI-19/verify-20260912T155027Z-3941/result.json) retain the dated evidence and exact source hashes.

The [project guide](lean/README.md), [formalization manifest](lean/formalization.yaml), and [independent reviews](lean/reviews/) document attribution, fidelity, and scope. These are independent AI-agent reviews, not external human peer review. On a Linux host satisfying the [verification prerequisites](../../tools/lean/HARNESS.md), run the following from the repository root at the pinned proof revision:

```
tools/lean/bootstrap.sh /tmp/nla-lean-tools
tools/lean/verify.sh \
  matrix-inequalities-and-norms/MI-19/lean /tmp/nla-lean-tools
```

## Problem statement

Let $n\ge2$, let $A=(a_{ij})\in\mathbb C^{n\times n}$ be Hermitian positive semidefinite, and let $q\in[0,1]$. Define
$$
\operatorname{inv}(\sigma)=\#\{(i,j):i<j,\ \sigma(i)>\sigma(j)\},\qquad
P_q(A)=\sum_{\sigma\in S_n}q^{\operatorname{inv}(\sigma)}
\prod_{i=1}^n a_{i,\sigma(i)},
$$
with $0^0=1$. Is it true that every nonempty proper subset $S\subset\{1,\ldots,n\}$ satisfies
$$
P_q(A)\ge
\sum_{\substack{\sigma\in S_n\\ \sigma(S)=S}}
q^{\operatorname{inv}(\sigma)}\prod_{i=1}^n a_{i,\sigma(i)}?
$$
Here $\sigma(S)=S$ means setwise preservation. The inversion counts on the right are taken in the full ordering $1,\ldots,n$.

## Relevance and ratings

 This is a block comparison for a matrix function interpolating determinant and permanent. At $q=1$ it reduces to a known permanental block inequality. For general $q$, ordering matters: the right side must not be replaced by a product of q-permanents of the two principal submatrices for an arbitrary subset.

## References

- R. B. Bapat and A. K. Lal, *Inequalities for the q-permanent*, Linear Algebra and its Applications 197–198 (1994), 397–409 ([original paper](https://doi.org/10.1016/0024-3795(94)90497-9)).
- C. M. da Fonseca, *The $\mu$-permanent revisited* (2018), §5, Conjecture 3 and Theorem 5.1 ([primary manuscript](https://arxiv.org/pdf/1804.02231)).

## Status check — 2026-09-10

 Da Fonseca explicitly states this conjecture, attributes it to Bapat and Lal, and distinguishes proved initial-segment cases from arbitrary subsets. Searches for “q-permanent”, “mu-permanent”, “Lieb”, “subset”, “conjecture”, and “proof”, including 2025–2026, found no general resolution. The newest explicit formulation located is from 2018, so this entry has weaker recent status evidence than the other candidates. The separately refuted permanent-on-top conjecture is not included.

**Independent audit:** Independently rechecked da Fonseca Conjecture 3 and Theorem 5.1 and searched for later subset-preserving q-permanent results. Initial segments form a proved subfamily; arbitrary subsets remain unresolved in the sources located.
