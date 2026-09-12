# TR-15 — Nonnegative H-eigenvalue inheritance from odd-order Hankel tensors

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Rating rationale:** Challenging because odd-order H-eigenvalue positivity lacks the even-order polynomial-positivity argument; specialist importance lies in transferring spectral certificates within Hankel representations.  
**Last checked:** 2026-09-12
**Status:** Lean verified

## Lean proof and verification evidence - 2026-09-12

**The complete odd-order inheritance conjecture is false, with a Lean-verified counterexample.** The [proof at revision 6a2d086](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/6a2d0868e8b7905dbd5c04d4beaae8cf43288e1f/tensor-computations/TR-15/lean) uses $`m=3`$, $`q=2`$, $`n=2`$ and the shared generator $`h=(2,0,1,0,2,0,-1)`$. Every real H-eigenvalue of the lower tensor is strictly positive, while the upper tensor has the exact H-eigenpair $`(-1,(0,1))`$.

**Mathematical counterexample and informal proof:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance.

The definitions retain every original odd $`m\ge3`$, integer $`q\ge2`$, dimension $`n\ge2`$ and real common generator. They use the actual Hankel entries, every ordered contraction tuple, signed coordinate powers and nonzero real H-eigenvectors. The seven [checked exports](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/6a2d0868e8b7905dbd5c04d4beaae8cf43288e1f/tensor-computations/TR-15/lean/Solution.lean), each with prefix `NLA.TR15.`, are:

- `lower_contractions`: all three exact component polynomials for every real vector.
- `upper_contraction`: the actual order-six contraction at $`(0,1)`$.
- `lower_eigenvalues_pos`: positivity of every lower real H-eigenvalue.
- `lower_eigenpair_exists`: a genuine nonzero lower pair from the intermediate value theorem.
- `upper_negative_eigenpair`: the complete upper pair and strict negative eigenvalue.
- `counterexample`: original admissibility, the lower premise and failure of the upper conclusion.
- `not_inheritanceConjecture`: negation of the complete universal inheritance assertion.

Lower positivity follows from the first contraction, a strictly positive sum of squares. The upper contraction has one surviving ordered tuple. An actual intermediate-value root supplies the lower pair; its existence is proved without adding a premise or a strong-Hankel hypothesis.

Two independent agents approved the [statements and completed proof](lean/reviews/). [Linux run 34716902324](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34716902324) matched all seven exports with the sandboxed Comparator and replayed the solution in Lean's default kernel. The [original artifacts and independent audit](lean/verification/linux-2026-09-12/) bind all 135 input hashes and both actual isolation/rejection-control suites. All 15 [internal/public transitive axiom reports](lean/verification/linux-2026-09-12/axiom-verification.json) use only `propext`, `Classical.choice` and `Quot.sound`. These are independent agent reviews, without a claim of external human peer review.

The proof pins **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). The kernel-mode LeanCert certificate $`-1<0`$ remains in the final negative-pair contradiction. See the [manifest](lean/formalization.yaml), [dependency pins](lean/lake-manifest.json) and [exact targets](lean/NUMERICAL_TARGETS.md). From the verified revision on a documented [non-root Linux host](../../tools/lean/HARNESS.md), reproduce with:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  tensor-computations/TR-15/lean \
  /absolute/path/to/nla-lean-tools
```

<!-- colbrook-unclaimed -->
## Resolution — 2026-09-11

**Negative resolution.** Matthew J. Colbrook's [complete manuscript, Counterexample proposition and proof](../../references/colbrook-unclaimed-2026-09-11/manuscripts/TR-15.md) disproves the universal conjecture with $`m=3`$, $`q=2`$, $`n=2`$ and the common generating vector $`h=(2,0,1,0,2,0,-1)`$. Every real H-eigenvalue of the order-three, dimension-three tensor $`A`$ is strictly positive, whereas the order-six, dimension-two tensor $`B`$ has the exact H-eigenpair $`(-1,(0,1))`$. The manuscript also proves that $`A`$ has a real H-eigenpair, so its premise is nonvacuous. The counterexample meets the original odd-lower-order assumptions; it does not contradict the separate even-lower-order theorem or results requiring a positive-semidefinite associated Hankel matrix.

The complete source passed [independent Codex-agent proof review](../../references/colbrook-unclaimed-2026-09-11/verification/reviews/TR-15-review.md). [Authorship, AI assistance and verification record](../../references/colbrook-unclaimed-2026-09-11/README.md). The 2026-09-11 review did not assert external human peer review or formal verification. The later Lean verification above covers the complete original implication and proves the premise is nonvacuous. The original target below is retained verbatim; the difficulty, importance and rating rationale above are historical. This entry no longer contributes to the open count.

[Manuscript PDF](../../references/colbrook-unclaimed-2026-09-11/manuscripts/TR-15.pdf). 
<!-- /colbrook-unclaimed -->

## Statement

For every odd $`m\ge3`$, integer $`q\ge2`$, dimension $`n\ge2`$, and vector $`h\in\mathbb R^{qm(n-1)+1}`$, define Hankel tensors $`A`$ and $`B`$ with this same generating vector. Their orders and dimensions are

```math
\mathop{\mathrm{order}}\nolimits(A)=m,\quad\dim(A)=q(n-1)+1,
\qquad \mathop{\mathrm{order}}\nolimits(B)=qm,\quad\dim(B)=n.
```

An order-$`s`$, dimension-$`N`$ Hankel tensor has entry $`h_{i_1+\cdots+i_s-s}`$, with each index in $`\{1,\ldots,N\}`$.

For a real order-$`s`$ tensor $`C`$, an H-eigenvalue is a real $`\lambda`$ admitting a real nonzero vector $`x`$ such that, for every $`i`$,

```math
\sum_{i_2,\ldots,i_s=1}^N C_{i i_2\cdots i_s}x_{i_2}\cdots x_{i_s}
=\lambda x_i^{s-1}.
```

Conjecture: if $`A`$ has no negative H-eigenvalues, then $`B`$ has no negative H-eigenvalues.

## Relevance

The question transfers a spectral positivity certificate between different Hankel representations of the same data, relevant to structured tensor eigenvalue computation and polynomial positivity.

## References

1. W. Ding, L. Qi, and Y. Wei, *Inheritance properties and sum-of-squares decomposition of Hankel tensors: theory and algorithms*, BIT Numer. Math. 57 (2017), 169–190. [DOI](https://doi.org/10.1007/s10543-016-0622-0); [author PDF](https://www.polyu.edu.hk/ama/staff/new/qilq/BIT-DQW.pdf), final §4, “The third inheritance property of Hankel tensors,” concluding conjecture; §2 gives order/dimension conventions.
2. L. Qi, *Hankel Tensors: Associated Hankel Matrices and Vandermonde Decomposition*, 2014. [Primary preprint](https://arxiv.org/pdf/1310.5470), §5, concerning H-eigenvalues and complete Hankel tensors.

## Status check — 2026-09-10

Rechecked the [Ding–Qi–Wei journal text, final §4](https://www.polyu.edu.hk/ama/staff/new/qilq/BIT-DQW.pdf), and searched for proofs or counterexamples to the third inheritance property. The source explicitly leaves odd lower order unresolved; its even-lower-order result lies outside the displayed target. Complete or strong Hankel hypotheses would be additional restrictions. No later resolution was located; this remains a bounded historical-source check.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
