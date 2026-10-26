# TR-06 — Finite mean angular condition number for identifiable tensor decomposition

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Rating rationale:** Challenging because generic uniqueness does not supply the integrability estimates needed near degenerate decompositions; specialist importance reflects the particular angular condition number and volume-based input model.  
**Status:** Lean verified  
**Last checked:** 2026-10-23  

<!-- lean-tr06-complete-2026-10-23 -->
## Lean proof and verification evidence — 23 October 2026

The [complete Lean proof](lean/Solution.lean) establishes the unchanged intrinsic volume-Gaussian finite-mean target and all ten original published candidate theorem statements. The [actual Linux run](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/40035041685) passed Comparator, the default kernel, LeanCert kernel mode and all rejection/isolation controls at exact proof commit `2b049df5`. Two [strict receipt replays](../../docs/lean/proofs/TR-06/verification/linux-ci/2b049df5/) passed all 45 controls and all 153 checked package inputs, including 144 Lean sources. Every selected theorem uses only the three standard Lean axioms.

The [independent complete-source audit](../../docs/lean/proofs/TR-06/campaign-2026-10-18/verification/CANONICAL_144_APPROVAL_2026-10-23.json) rebuilt all 144 sources and checked the literal target, original theorem types and 772 declarations; it separately rejected all eleven intentional Challenge placeholders. The proof derives full-measure regularity, positive annular volume, finite volume of the actual whole normalized graph and angular integrability from the original hypotheses. All 58 retained candidate sources, the original mathematical target and permanent ID/path are preserved exactly.

[Original problem and manuscript archives](../../docs/lean/proofs/TR-06/originals-c4c7be59/manifest.json) retain the pre-verification files. Mathematical credit remains with Matthew J. Colbrook; retained formalization credit remains in its sources. New formal proofs and independent reviews are AI-agent work. The dated resolution and original statement below remain unchanged. Descriptive status/package changes receive a separate fresh Linux receipt; the checked Lean source bytes remain identical.
<!-- /lean-tr06-complete-2026-10-23 -->

<!-- colbrook-unclaimed -->
## Resolution — 2026-09-11

**Affirmative resolution.** Matthew J. Colbrook's [complete manuscript, theorem in §1 and proof in §§2–4](../../references/colbrook-unclaimed-2026-09-11/manuscripts/TR-06.md) proves finite mean angular condition number for every admissible format and every $`r\ge3`$ under the original generic complex identifiability assumption. The proof uses the exact volume-Gaussian input distribution and the derivative of the individually normalized summands. A bounded semialgebraic graph controls the angular derivative on the unit link; homogeneity then gives a finite radial integral. It does not assert a format-uniform bound or finite mean for the ordinary condition number.

The complete source passed [independent Codex-agent proof review](../../references/colbrook-unclaimed-2026-09-11/verification/reviews/TR-06-review.md). [Authorship, AI assistance and verification record](../../references/colbrook-unclaimed-2026-09-11/README.md). No external human peer review or formal verification is asserted. The original target below is retained verbatim; the difficulty, importance and rating rationale above are historical. This entry no longer contributes to the open count.

[Manuscript PDF](../../references/colbrook-unclaimed-2026-09-11/manuscripts/TR-06.pdf). [Second independent review](../../references/colbrook-unclaimed-2026-09-11/verification/reviews/TR-06-second-review.md). 
<!-- /colbrook-unclaimed -->

## Context and notation

Fix $`d\ge3`$, $`n_j\ge2`$, and $`r\ge2`$. Assume generic complex identifiability: outside a proper algebraic exceptional set, a complex tensor of rank $`r`$ in this format has a unique unordered collection of $`r`$ rank-one summands. Let $`M_r`$ be the smooth identifiable locus of real rank-$`r`$ tensors, with induced Euclidean volume $`dV`$. The random input has density

```math
d\mu(A)=Z^{-1}e^{-\|A\|_F^2/2}\,dV(A).
```

For the addition map $`\Phi(a_1,\ldots,a_r)=\sum_i a_i`$ on rank-one tensors, let $`\Psi`$ be a local inverse at $`A`$. Use Frobenius norms and their product norm. Define

```math
\kappa(A)=\|D\Psi(A)\|_2,\qquad
\kappa_{\rm ang}(A)=\|D(p^{\times r}\circ\Psi)(A)\|_2,
\quad p(a)=a/\|a\|_F.
```

Values on measure-zero exceptional sets do not affect the expectations. This samples tensors by volume, not independent Gaussian summands.

## Problem statement

Under this probability model, prove or disprove

```math
\mathbb E_\mu\kappa_{\rm ang}(A)<\infty
```

for every admissible format and $`r\ge3`$. The rank-two case is a theorem. Normalizing each recovered summand inside the derivative is part of the definition; simply dividing the regular condition number by a scalar does not give this problem.

## Reference

Beltrán, Breiding, and Vannieuwenhoven, [*The Average Condition Number of Most Tensor Rank Decomposition Problems Is Infinite*](https://doi.org/10.1007/s10208-022-09551-1), *Foundations of Computational Mathematics* 23 (2023), 433–491: equation (6), Theorem 3, and Conjecture 2. The [author preprint](https://arxiv.org/pdf/1903.05527) labels the conjecture 1.10.

## Status check — 2026-09-10

Rechecked the [journal version, equation (6), Theorem 3 and Conjecture 2](https://doi.org/10.1007/s10208-022-09551-1), and searched for higher-rank angular-condition-number proofs. The theorem covers rank two, which the displayed target already excludes; no result proving finite mean for all admissible ranks at least three was located. The 2023 conjecture is the latest explicit statement checked, and a later unlocated result cannot be ruled out.

