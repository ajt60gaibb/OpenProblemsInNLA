# MD-04 — The Beck–Fiala discrepancy conjecture

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Provenance:** source-stated conjecture.  
**Status:** Lean verified
**Last checked:** 2026-10-16

**Rating rationale:** The unrestricted square-root sparsity law is a central discrepancy conjecture with broad consequences for combinatorics, rounding and optimization.

## Resolution — 2026-09-11

**Affirmative resolution by Shengtao Guo, Ethan X. Fang and Junwei Lu**, [*Vector Balancing via Directional Total Variation*, arXiv:2609.11189v1](https://arxiv.org/abs/2609.11189v1), submitted 10 September 2026, **Corollary 1.2, p. 2**. It proves the displayed target with $`C=3\sqrt{2\pi}`$ for every allowed $`m,n,t`$, including the smaller sparsities left unresolved by the earlier results. Since a $`0`$–$`1`$ column has squared Euclidean norm equal to its number of nonzero entries, apply Theorem 1.1 to $`A/\sqrt t`$ and multiply the strict discrepancy bound by $`\sqrt t`$. Every column receives a sign.

**Application note by George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology: [proof by reference](solution.md), **Theorem 2** ([PDF](../../references/stepaniants-2026-09-11/manuscripts/md03_md04_proofs.pdf) · [LaTeX](../../references/stepaniants-2026-09-11/manuscripts/md03_md04_proofs.tex)). Stepaniants authors the explanatory note; both the theorem and its Beck–Fiala corollary are credited to Guo, Fang and Lu.

A separate Codex agent checked the application and substantive source proof and returned **PASS**: [independent review](../../references/stepaniants-2026-09-11/verification/reviews/MD-03-MD-04-review.md). Verification is independent automated-agent review, not external human peer review or formal certification. The source remains a preprint and discloses Odin AI use; the application draft was prepared with ChatGPT. No case of the original target remains open under the reviewed result. The original statement and earlier status evidence remain below, and the ratings above are historical. [Submission record](../../references/stepaniants-2026-09-11/README.md).

## Lean proof and verification evidence

The [Lean solution](lean/Solution.lean) proves the complete original existential target with universal constant `C = 36`. It imports the pinned formal Komlós theorem of Gabriel Dahia through the [MD-03 bridge](lean/NLA/MD03/Proof.lean), then applies the [source-locked scaling reduction](lean/NLA/MD04/Reduction.lean) to each `{0,1}` matrix at every allowed sparsity. The historical Guo–Fang–Lu result above gives the sharper value `3√(2π)`; the original question asks only whether some dimension-independent positive constant exists. Neither the original target nor its permanent ID has changed.

An [independent AI mathematical and proof review](../../docs/lean/proofs/MD-04/INDEPENDENT_REVIEW.md) checked every quantifier, endpoint, entry and sign condition, and the exact rescaling argument against the frozen Lean statement. The [13 October isolated Ubuntu Comparator job](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/38392383534/job/115299684643) built the separate Challenge and Solution, checked `NLA.MD04.target` with Lean's default kernel, and reported only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. Its [downloaded artifact and source-hash receipt](../../docs/lean/proofs/MD-04/LINUX_CI_RECEIPT.md) bind all proof inputs and the exact comparator result. The Challenge has one deliberate comparison-hole `sorry`; it is not imported by Solution. This is Lean kernel verification of the displayed target, not external human peer review or a formalization of the sharper historical constant.

## Problem statement

Does a finite universal constant $`C>0`$ exist such that the following holds for every pair of positive integers $`m,n`$, every integer $`t`$ with $`1\leq t\leq m`$, and every matrix $`A=(a_{ij})\in\{0,1\}^{m\times n}`$?
If

```math
\sum_{i=1}^m a_{ij}\leq t\qquad(1\leq j\leq n),
```

then some signing $`x\in\{-1,1\}^n`$ satisfies

```math
\|Ax\|_\infty\leq C\sqrt t.
```

The constant must be independent of $`m,n,t`$. All columns are available when choosing the signing. The zero-sparsity case is trivial and excluded from the quantifiers.

The matrix is the incidence matrix of a set system: each element belongs to at most $`t`$ sets, and the signing should balance every set. The problem asks whether column sparsity alone controls the simultaneous row error at its conjectured square-root scale. It is a special case of the Komlós conjecture after column normalization, but an independent classical source-stated conjecture for incidence matrices.

## References

1. D. J. Altschuler and K. Tikhomirov, *Online Beck–Fiala Down to Logarithmic Sparsity*, arXiv:2607.14238 (2026), abstract and introduction: the unrestricted conjecture and the proved sparsity regime. [Paper](https://arxiv.org/html/2607.14238v1).
2. N. Bansal and H. Jiang, *Decoupling via Affine Spectral-Independence: Beck-Fiala and Komlós Bounds Beyond Banaszczyk*, arXiv:2508.03961v2 (2025), abstract and introductory results. [Paper](https://arxiv.org/abs/2508.03961).
3. J. Beck and T. Fiala, *“Integer-making” theorems*, Discrete Applied Mathematics 3(1) (1981), pp. 1–8, the original bounded-column-sparsity discrepancy results. [Article](https://doi.org/10.1016/0166-218X(81)90022-6).

## Earlier status check — 2026-09-10

checked 2607.14238v1 (2026-07-15), 2508.03961v2 (2025-09-09), and searches “Beck Fiala conjecture solved 2026 logarithmic sparsity” and “Online Beck Fiala Down to Logarithmic Sparsity”. The 2026 work reaches sparsities $`t\geq(\log n)^{1+o(1)}`$ in its notation translated to $`n`$ columns; it does not establish the assertion for all sparsities. Online lower bounds concern a more restrictive information model. No full resolution or withdrawal was found.

**Audit update (2026-09-10):** Rechecked the July 2026 online/offline paper and searched for unrestricted Beck–Fiala results. It proves the offline target in a substantial sparsity regime, which is part of the displayed family, but leaves smaller sparsities unresolved. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
