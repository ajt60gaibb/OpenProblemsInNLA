# TR-13 — Equality of ranks for generic odd-order Hankel tensors

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Rating rationale:** Challenging because the remaining odd orders require rank lower bounds beyond the proved even-order and cubic mechanisms; specialist importance reflects the restriction to generic Hankel tensors.  
**Last checked:** 2026-10-13  
**Status:** Lean verified  

<!-- colbrook-recovered-tensors -->
## Resolution — 2026-09-11

**Affirmative resolution by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. For every odd $`m\ge5`$ and $`n\ge2`$, a nonempty Zariski-open set of complex Hankel tensors has ordinary rank, symmetric rank, ordinary border rank, symmetric border rank and Vandermonde rank all equal to $`\lceil(m(n-1)+1)/2\rceil`$. A compressed three-slice Koszul flattening gives the ordinary-border-rank lower bound, including arbitrary unstructured limiting sequences; a dominant moment map supplies the matching actual Vandermonde-rank upper bound. Exceptional Hankel tensors and the separate all-tensors question TR-14 are not settled.

[Complete manuscript, Theorem 1 and Sections 2–5](../../references/colbrook-recovered-tensors-2026-09-11/manuscripts/TR-13.pdf) · [Standalone TeX](../../references/colbrook-recovered-tensors-2026-09-11/manuscripts/TR-13.tex) · [Independent complete-source PASS review](../../references/colbrook-recovered-tensors-2026-09-11/verification/reviews/TR-13-review.md) · [Authorship and provenance](../../references/colbrook-recovered-tensors-2026-09-11/README.md).

The recovered AI-assisted proof passed independent agent review; this is not external human peer review or formal certification. The original target and dated source audit are retained. Difficulty, importance and rating rationale are historical. No novelty or priority claim is made.
<!-- /colbrook-recovered-tensors -->

## Complete Lean formalization — 28 September 2026

A [complete Lean proof](https://github.com/marcusdavidwebb/OpenProblemsInNLA/tree/a95148f74de9b452e2f0df04aaf135bef627183e/tensor-computations/TR-13/lean) now proves the entire retained target, including
every odd $`m\ge5`$, every $`n\ge2`$, and all five ranks. The declaration
`NLA.TR13.generic_rank_equality` constructs a nonempty principal Zariski-open
set and proves the common value $`\lceil(m(n-1)+1)/2\rceil`$. Ordinary-border
limits range over arbitrary tensors in the full ambient space. The definitions,
source correspondence and exact conventions are documented in the
[project README](lean/README.md) and [frozen targets](lean/NUMERICAL_TARGETS.md).

**Local verification:** Lean 4.33.1 with Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`; all transitive dependencies are pinned.
The [successful macOS build and axiom report](lean/verification/macos-full.log)
checks the complete declaration and records only `propext`, `Classical.choice`
and `Quot.sound`. The solution contains no unfinished proof or custom axiom;
the separate comparison challenge is never imported by it. Reproduction
commands and source hashes are retained in [verification](lean/verification/README.md).

The later [independent all-width statement review](../../docs/lean/proofs/TR-13/EXACT_STATEMENT_INDEPENDENT_REVIEW.md)
and [isolated Linux Comparator/LeanCert receipt](../../docs/lean/proofs/TR-13/LINUX_CI_RECEIPT.md)
completed the verification gates in the [evidence section](#lean-proof-and-verification-evidence). The reviewer notes that the
local and frozen targets live in separate Lake projects, so their mathematical
correspondence is source reviewed rather than expressed by one cross-project theorem.

The implementation was generated with OpenAI Codex agents. Matthew J. Colbrook
retains credit for the mathematical resolution, and Nie and Ye for the
conjecture and prior results. The formalization uses an elementary Prony
reconstruction for the upper bound and a uniform Koszul certificate, including
the binary case. No human or source-author endorsement is claimed.

## Lean proof and verification evidence

**Reviewed 13 October 2026.**

At immutable repository revision [`bca7904b`](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/bca7904b8d6f43b7258bc0eaed636a2b6b4a8792/tensor-computations/TR-13/lean/Solution.lean), `NLA.TR13.generic_rank_equality` gives the common exact rank for every odd $`m\ge5`$ and $`n\ge2`$, while `NLA.TR13.generic_width_equivalence` proves the retained equivalence at every natural width. The [independent comparison with the frozen target](../../docs/lean/proofs/TR-13/EXACT_STATEMENT_INDEPENDENT_REVIEW.md) checks the nonempty principal open set, all five rank notions, unrestricted ordinary-border limits, and the absence of an added premise or weaker conclusion.

The [manifest](lean/lake-manifest.json) pins Lean **4.33.1**, Mathlib `0df444a360ea`, and LeanCert `621a43d7cf21`. From `tensor-computations/TR-13/lean`, run `lake build Challenge Solution`. The [10 October Linux job and log](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/38006337671/job/114076129861) passed Comparator and kernel trust for both selected exports; their transitive axiom sets contain only `propext`, `Classical.choice`, and `Quot.sound`. The [receipt](../../docs/lean/proofs/TR-13/LINUX_CI_RECEIPT.md) records the successful revision and reproduction context. This catalog reviewed that public verification record; it did not rerun Lean locally for this status update.

## Statement

Fix an odd integer $`m\ge5`$ and $`n\ge2`$. A complex Hankel tensor $`H`$ of order $`m`$ and dimension $`n`$ has entries

```math
H_{i_1\ldots i_m}=h_{i_1+\cdots+i_m-m},\qquad 1\le i_j\le n,
```

for $`h\in\mathbb C^{m(n-1)+1}`$. Is there a nonempty Zariski-open subset of this Hankel tensor space on which

```math
R(H)=R_{\rm sym}(H)=\underline R(H)=\underline R_{\rm sym}(H)=R_V(H)?
```

Here $`R`$ is the minimum number of arbitrary complex rank-one tensor summands; $`R_{\rm sym}`$ restricts summands to complex multiples of $`v^{\otimes m}`$. Each underlined border rank is the least integer $`r`$ admitting a sequence of complex tensors of the corresponding rank at most $`r`$ converging entrywise to $`H`$. $`R_V`$ further restricts $`v`$ to

```math
v(a,b)=(a^{n-1},a^{n-2}b,\ldots,b^{n-1}),\quad (a,b)\ne(0,0).
```

Thus limits defining symmetric border rank stay in the symmetric tensor space; limits defining ordinary border rank need not. Generically $`R_V=\lceil(m(n-1)+1)/2\rceil`$.

## Relevance

Hankel tensor decompositions encode sums of exponentials used in signal reconstruction. The conjecture compares structured decomposition lengths with the best unconstrained low-rank descriptions.

## References

1. J. Nie and K. Ye, *Hankel Tensor Decompositions and Ranks*, SIAM J. Matrix Anal. Appl. 40 (2019). [DOI](https://epubs.siam.org/doi/10.1137/18M1168285); [author preprint](https://arxiv.org/pdf/1706.03631), §6, Question 6.1 and Conjecture 6.2, p.16; Corollary 3.3 gives the generic Vandermonde rank.
2. L. Qi, *Hankel Tensors: Associated Hankel Matrices and Vandermonde Decomposition*, 2014. [Primary preprint](https://arxiv.org/pdf/1310.5470), §1, equation (1), and §4, Theorem 3, for the structured decomposition background.

## Status check — 2026-09-10

Rechecked [Nie–Ye, §6, Question 6.1 and Conjecture 6.2](https://arxiv.org/pdf/1706.03631), and searched the conjecture number and later odd-order Hankel-rank literature. The general odd-order target remains conjectural in that source; its even-order and order-three theorems are already excluded here. No later proof or counterexample was located. Status rests on the 2019 primary text plus this bounded search.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
