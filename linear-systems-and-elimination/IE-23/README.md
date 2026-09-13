# IE-23 — Uniqueness of the right inverse minimizing an induced p-to-2 norm

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** hard  
**Importance:** interesting to specialist  
**Status:** Lean verified
**Last checked:** 2026-09-12

<!-- colbrook-recovered -->
## Independently reviewed resolution - 2026-09-11

**Negative resolution.** Theorem 1 gives a $`2\times3`$ full-row-rank matrix with distinct norm-minimizing right inverses for every $`2< p<\infty`$ over both fields. Their common induced norm is $`2^{1/2-1/p}`$. Sections 3-4 identify the complete minimizer sets, including a complex higher-dimensional family. The smallest matrix is attributed to Dokmanic and Gribonval\'s spectral-norm example; its extension to the displayed direct-inverse objective is checked. No conclusion about the separate product objective is claimed.

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. [Complete manuscript](../../references/colbrook-recovered-2026-09-11/manuscripts/IE-23.pdf), [independent proof review](../../references/colbrook-recovered-2026-09-11/verification/reviews/IE-23-review.md), and [submission record](../../references/colbrook-recovered-2026-09-11/README.md). The supplied notes were reconstructed with substantial AI assistance. That original review was informal; the later Lean verification of the canonical negative answer is documented below. External human peer review, novelty and priority are not claimed.

The difficulty, importance and rating rationale below are historical assessments of the original open target. Original statements, references and dated audits are preserved.
<!-- /colbrook-recovered -->

**Rating rationale:** Hard reflects a focused uniqueness question for a known norm minimizer; specialist impact is the characterization of generalized inverses under induced norms.

## Lean proof and verification evidence - 2026-09-12

**The complete original uniqueness conjecture is Lean verified, with a negative answer.** The [proof at revision a40e560](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/a40e5608f61dd4086708cb2e03901ffd01e4c0a9/linear-systems-and-elimination/IE-23/lean) uses the unchanged rational $`2\times3`$ example at $`p=4`$. Two distinct right inverses attain the same actual induced norm $`\sqrt{\sqrt{2}}`$ and are global minimizers over **every complex right inverse**. The formalization proves genuine matrix rank and inverse identities, real-power and Euclidean-norm bounds, and the actual supremum over all nonzero complex inputs. The generic norm semantics cover every original dimension and finite real $`p>2`$; no additional boundedness or minimality premise is assumed.

**Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. **Matthew J. Colbrook** retains mathematical authorship of the resolution; **Ivan Dokmanić and Rémi Gribonval** retain credit for the underlying example and original uniqueness question.

The eight [checked exports](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/a40e5608f61dd4086708cb2e03901ffd01e4c0a9/linear-systems-and-elimination/IE-23/lean/Solution.lean), each with prefix `NLA.IE23.`, are:

- `inducedNorm_semantics`: actual nonzero-input supremum and all-input norm inequality.
- `witness_matrix_identities`: full row rank, true inverse, both right inverses and distinctness.
- `fourth_power_norm_control`: exact real-power identities and universal complex-vector bound.
- `witness_action_identities`: actual actions and the bound for every right-inverse competitor.
- `witness_attainment`: a genuine nonzero vector attains both norm ratios.
- `witness_norms`: both actual suprema equal the positive fourth root of two.
- `witness_global_minimizers`: both matrices globally minimize the entire feasible norm set.
- `not_rightInverseUniqueConjecture`: the full original universal assertion is false.

Two independent agents approved the [statements and completed proof](lean/reviews/). [Ubuntu run 34725525250](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34725525250) matched all eight declarations with the sandboxed Comparator and replayed the solution in Lean's default kernel. The [original artifacts and operational audit](lean/verification/linux-2026-09-12/) bind all 190 submitted inputs and both actual isolation/rejection-control suites. All 16 [internal/public axiom reports](lean/verification/linux-2026-09-12/axiom-verification.json) use exactly `propext`, `Classical.choice` and `Quot.sound`. The proof author performed the operational inspection; the coordinator, independently of that author, [accepted the actual evidence](lean/verification/root-operational-2026-09-12/ROOT-CHECKS.json). These operational roles are separate from the two mathematical referees. External human peer review is not claimed.

The pins are **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). LeanCert audits the kernel trust of this pure exact proof; there is **no numerical interval certificate**. The $`p=4`$ sum-of-squares argument avoids approximate norm calculations and interval subdivision. The source's stronger all-$`p`$ formulas, complete minimizer classifications and higher-dimensional families retain their manuscript and informal-review scope; the eight exports give the complete original negative answer. See the [project guide](lean/README.md), [manifest](lean/formalization.yaml) and [dependency pins](lean/lake-manifest.json). From the immutable verified revision on a documented [non-root Linux host](../../tools/lean/HARNESS.md), reproduce with:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  linear-systems-and-elimination/IE-23/lean \
  /absolute/path/to/nla-lean-tools
```

## Problem statement

Let $`1\le m< n`$, let $`A\in\mathbb C^{m\times n}`$ have rank $`m`$, and let $`2< p<\infty`$. For $`X\in\mathbb C^{n\times m}`$ define the induced norm

```math
\|X\|_{p\to2}=\sup_{y\in\mathbb C^m\setminus\{0\}}
\frac{\|Xy\|_2}{\bigl(\sum_{i=1}^m|y_i|^p\bigr)^{1/p}}.
```

The Moore–Penrose inverse $`A^\dagger=A^*(AA^*)^{-1}`$ minimizes this norm among the right inverses $`X`$ satisfying $`AX=I_m`$. Is it always the unique minimizer? Equivalently, must

```math
AX=I_m,\quad X\ne A^\dagger
\quad\Longrightarrow\quad
\|X\|_{p\to2}>\|A^\dagger\|_{p\to2}
```

hold for every such $`A,p,X`$?

This is the direct-inverse uniqueness question in Dokmanić–Gribonval's Remark 4.1. The endpoints and the separate objective $`\|XA\|_{p\to2}`$ are outside this statement.

## Connection to numerical linear algebra

The norm measures the worst Euclidean solution amplification for right-hand sides bounded in $`\ell^p`$. Uniqueness determines whether another linear solver can match the Moore–Penrose inverse's optimal amplification while changing its sparsity or structure.

## References

1. I. Dokmanić and R. Gribonval, *Beyond Moore–Penrose Part I: Generalized Inverses that Minimize Matrix Norms*, arXiv:1706.08349v2 (2017), §2.1 and §2.4 (right inverses and $`A^\dagger`$); §4.4, Corollary 4.2(3) and Remark 4.1, manuscript p. 18 (PDF page 18). [Preprint and version history](https://arxiv.org/abs/1706.08349). [PDF](https://arxiv.org/pdf/1706.08349).
2. I. Dokmanić and R. Gribonval, [*Part II: The Sparse Pseudoinverse*](https://arxiv.org/abs/1706.08701), 2017, §2. Its entrywise-norm objective is different.

## Earlier status check — 2026-09-08

Checked the complete v2 statement and version history on 2026-09-08; v2, dated 2017-07-13, remains the latest arXiv version of Part I. Searches combined the authors, the paper title, “induced norm”, “p to 2”, “unique”, “uniqueness”, “generalized inverse”, and 2025/2026. The companion paper's sparse-inverse uniqueness results concern entrywise norms and generic inputs, not this induced-norm claim for every full-row-rank matrix. No later proof or counterexample was located. This bounded search does not certify that no resolution exists elsewhere.

## Audit update — 2026-09-10

The [author copy of Part I](https://dokmanic.ece.illinois.edu/assets/pdf/DokmanicG17aa.pdf), Corollary 4.2(3) and Remark 4.1 on printed p. 18, explicitly separates minimality from the remaining uniqueness question for $`2< p<\infty`$. Searches for later induced-$`p`$-to-2 uniqueness results found no resolution; Part II's sparse-inverse objectives do not supply this missing assertion.
