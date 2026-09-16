# MF-12 — Realizing arbitrary polynomial growth exponents by finite matrix families

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because finite families must realize every exponent at every length; community impact connects switched dynamics and asymptotic matrix-product growth.  
**Status:** Lean verified

**Last checked:** 2026-09-15

<!-- colbrook-jsr-growth -->
## Resolution — 2026-09-11

**Affirmative resolution.** Matthew J. Colbrook's [complete manuscript, Theorem 1 and its proof in §§2–5](../../references/colbrook-jsr-growth-2026-09-11/manuscripts/arbitrary_growth_exponents.pdf) constructs two distinct real matrices for every real $`\alpha\ge0`$, with joint spectral radius one and maximal length-$`k`$ product norm between positive constant multiples of $`k^\alpha`$ for every integer $`k\ge1`$. The matrices and dimension are fixed once the exponent is chosen. Six-dimensional pairs suffice for $`0<\alpha<1`$; every nonnegative rational exponent can be realized with dyadic-rational entries. The proof covers all switching words for the upper bound and every length for the lower bound, including small lengths. It asserts comparability, not convergence of the normalized growth sequence.

The complete original proof passed [independent Codex-agent review](../../references/colbrook-jsr-growth-2026-09-11/verification/reviews/MF-12-review.md). [Authored TeX](../../references/colbrook-jsr-growth-2026-09-11/manuscripts/arbitrary_growth_exponents.tex) · [Submission, authorship and verification record](../../references/colbrook-jsr-growth-2026-09-11/README.md). The proof was developed with AI assistance. Those original reviews were informal; the separate Lean verification of the complete original target is documented below. No external human peer review is claimed. The original statement and prior evidence below are retained, and the ratings above are historical. This entry no longer contributes to the open count.

<!-- /colbrook-jsr-growth -->

## Lean proof and verification evidence

**Formalization: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology.** Matthew J. Colbrook retains credit for the original mathematical proof. The [complete Lean proof at immutable revision 3d06c496](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/3d06c49635bbdde109c491510641204285eaf05c/matrix-functions-and-stability/MF-12/lean/Solution.lean) pins Lean **4.33.1**, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`.

The declaration `NLA.MF12.realizes_every_nonnegative_exponent` proves the complete original target: for every real exponent $`\alpha\ge0`$, a fixed positive dimension and exactly two distinct fixed real matrices have an attained maximum of genuine Euclidean operator norms between fixed positive multiples of $`k^\alpha`$ for **every** integer $`k\ge1`$. The actual $`k`$th-root sequence converges to one. Dimensions, matrices and comparison constants are fixed before the length is quantified.

All **28 declarations** and their dependency bridges are listed in [formalization.yaml](lean/formalization.yaml) and matched against the independently reviewed [Challenge](lean/Challenge.lean). The [definitions](lean/NLA/MF12/Definitions.lean) retain all switching words, every positive length, exponent zero and arbitrary noninteger exponents. Exact algebra, finite Holder inequalities and rational bounds replace interval searches. Enlarged constants suffice for the original question; the manuscript's additional rational-entry and density results, sharper constants and optimal dimensions are outside the formalized scope.

On **15 September 2026**, [the actual GitHub Linux verification job](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35037011332/job/104608341268) checked this exact proof commit. All 28 targets passed LeanCert kernel-trust assertions, non-root sandboxed Comparator statement matching and Lean default-kernel replay. Their transitive axiom sets are only `propext`, `Classical.choice` and `Quot.sound`; `gap_decomposition` uses just `propext` and `Quot.sound`. Actual invalid-proof, mismatched-statement, forbidden-axiom and sandbox controls passed. The [retained logs, artifact and input hashes](lean/verification/linux-2026-09-15) bind this execution to all 322 candidate project files. No local macOS Lean execution is claimed.

Two independent AI-agent final referees accepted the complete source and actual evidence: [referee 1](lean/reviews/final/referee-elimination/REVIEW.md) and [referee 2](lean/reviews/final/referee-inequalities/REVIEW.md). They applied the repository's scoped Tau Ceti protocol; this is distinct from external human peer review or certification of checker-software infallibility.

For the ordinary proof build, enter [the Lean project](lean/README.md) with its pinned toolchain and run:

```
lake exe cache get && lake build
```

The default target is the complete Solution. For the additional Comparator, kernel and rejection checks, follow the [shared Linux instructions](../../docs/lean/README.md). Solution never imports Challenge's specification placeholders. This evidence names the exact checked proof revision; later publication commits require separate exact-commit checks.

## Context and notation

The joint spectral radius of a nonempty compact set $`\mathcal M\subset\mathbb C^{d\times d}`$ is

```math
\widehat\rho(\mathcal M)=\lim_{k\to\infty}
\max_{A_1,\ldots,A_k\in\mathcal M}\|A_k\cdots A_1\|_2^{1/k}.
```

This definition also applies to finite real matrix sets. The ordinary spectral
radius of one matrix is written $`\rho(A)`$.

For a compact nonempty $`\mathcal M\subset\mathbb R^{d\times d}`$ with
$`\widehat\rho(\mathcal M)=1`$, define its maximal product norm at length $`k`$ by

```math
g_{\mathcal M}(k)=\max_{A_1,\ldots,A_k\in\mathcal M}\|A_k\cdots A_1\|_2.
```

This problem concerns growth within one family over time. [MF-07](../MF-07/README.md) instead requests
a dimension-dependent bound uniform across families.

## Problem statement

For every real $`\alpha\ge0`$, do there exist a positive integer
$`d`$, a finite nonempty $`\mathcal M\subset\mathbb R^{d\times d}`$ with
$`\widehat\rho(\mathcal M)=1`$, and constants $`0< c\le C<\infty`$ such that

```math
c k^\alpha\le g_{\mathcal M}(k)\le C k^\alpha
\qquad\text{for every integer }k\ge1?
```

## Reference and status evidence

Varney and Morris,
[On marginal growth rates of matrix products](https://arxiv.org/html/2209.00449),
§7, Question 2. Corollary 6.1 realizes exponent $`1/3`$; the all-exponents question
remains posed. Searches for the title, authors, and marginal-growth exponents
through 2026 located no complete answer. Infinite compact families and
subsequence-only lower bounds do not meet the finite-family, every-length target.

## Audit — 2026-09-10

Rechecked [Varney–Morris, Corollary 6.1, Proposition 3.1, and Question 2](https://arxiv.org/html/2209.00449): exponent $`1/3`$ is realized and realizable exponents are closed under addition. The all-exponents assertion remains open. Author and marginal-growth-exponent searches found no complete finite-family construction or obstruction.
