# IE-06 — The square-root upper bound for Gaussian partial-pivoting growth

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Lean verified
**Last checked:** 2026-10-06

## Resolution — 2026-10-06

**Conjecture origin:** The conjecture goes back to Lloyd N. Trefethen and David Bau III, *Numerical Linear Algebra* (SIAM, 1997), p. 169.

**Affirmative resolution; Lean verified.** John Urschel's [*On the Growth Factor of Random Matrices*](https://arxiv.org/abs/2610.06785v1), posted 5 October 2026, resolves the square-root upper-bound target below: see **Theorem 1.4**, together with **Section 5.1 and the proof of Proposition 5.1** for growth over all Schur complements. The original problem statement and permanent ID are retained.

The complete Lean proof implements the original target and the stronger all-Schur tail. Independent Codex AI-agent reviews checked the mathematical correspondence, and the catalog's authoritative Linux pipeline accepted all six target declarations on 6 October 2026, including the full Comparator/exporter and raw-kernel checks. The [retained verification evidence](#lean-proof-and-verification-evidence) supports promotion to **Lean verified**.

The difficulty, importance and rating rationale are historical assessments of the original open target.

**Rating rationale:** Challenging reflects the need for a sharp probabilistic exponent beyond existing polynomial estimates; community impact is its prediction of typical partial-pivoting stability.

## Context and notation

All elimination in this problem is in exact arithmetic. Write $`\|A\|_{\max}=\max_{ij}|a_{ij}|`$. A pivoting path creates successive active Schur complements $`S_1=A,S_2,\ldots,S_n`$, with row/column permutations as appropriate. Its element-growth factor is

```math
\rho(A)=\frac{\max_{1\leq j\leq n}\|S_j\|_{\max}}{\|A\|_{\max}}.
```

Partial pivoting chooses a largest-magnitude entry in the active first column; complete pivoting chooses one anywhere in the active matrix. If ties occur, a universal statement includes every admissible tie choice; a supremum includes all admissible paths. These conventions remove implementation-dependent ambiguity. Matrices are nonsingular unless otherwise stated.

## Problem statement

Let $`G_n\in\mathbb R^{n\times n}`$ have independent $`N(0,1)`$ entries. Is the following precise square-root upper-bound conjecture true?

```math
\text{For every }\eta>0,\qquad
\lim_{n\to\infty}\Pr\{\rho_{\mathrm{PP}}(G_n)>n^{1/2+\eta}\}=0.
```

Here growth is measured over the exact-arithmetic Schur complements as defined above. This formulation asks only for the conjectured upper exponent; it does not add an unsupported matching lower-bound assertion or a limiting-distribution claim. It is also distinct from [IE-04](../IE-04/README.md), which requires a uniform result after perturbing every deterministic center and prescribes an exponential tail.

## Lean proof and verification evidence

**Authoritative Linux verification completed, 6 October 2026.** The maintainer reports that John Urschel gave permission to publish this Lean code. That permission is not a correctness endorsement. The [immutable proof source](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/263a215acd295a260dec7a75ff6bebebb9789df9/linear-systems-and-elimination/IE-06/lean/Solution.lean) at revision `263a215acd295a260dec7a75ff6bebebb9789df9` implements six declarations in namespace `NLA.IE06`:

- `squareRootUpperBound`: the complete original limit, for every real $`\eta>0`$.
- `schurSubpolynomialTail`: the stronger all-Schur tail, for every real $`\alpha>0`$ with constants independent of dimension.
- `gaussianMatrix_probability`: the actual independent standard-Gaussian entry law has mass one.
- `exceedanceEvent_measurable`: the literal growth event is measurable for every dimension and threshold.
- `admissiblePath_exists`: every nonsingular input admits a partial-pivoting path.
- `gaussianMatrix_singular_null`: singular inputs form a Gaussian null set.

The [final independent mathematical scope audit](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/263a215acd295a260dec7a75ff6bebebb9789df9/linear-systems-and-elimination/IE-06/lean/reviews/final-independent-mathematical-scope-audit.md) checks the original full statement, all active Schur stages, normalization, every admissible tie choice, and all probability quantifiers. The proof follows the manuscript's all-Schur argument; it does not identify the paper's displayed LU-growth definition with the catalog's growth factor. Every probabilistic premise of the final theorem is supplied by a proved Lean declaration. Reviews were performed by AI agents, not external human referees.

The [dated local receipt](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/263a215acd295a260dec7a75ff6bebebb9789df9/linear-systems-and-elimination/IE-06/lean/verification/local/attempt-0i_0ibma/result.json) records 114 successfully compiled source modules and a transitive axiom audit of all 3,229 owned declarations across 113 concrete modules, including private helpers. The unchanged pinned Comparator library [accepted all six actual theorem statements, referenced definitions, and proof axiom closures](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/263a215acd295a260dec7a75ff6bebebb9789df9/linear-systems-and-elimination/IE-06/lean/verification/local/attempt-0i_0ibma/CompareSolution.lean.log) against the independent frozen Challenge. LeanCert kernel checks passed; only `propext`, `Classical.choice`, and `Quot.sound` are permitted. The deliberate `sorry` and native-execution rejection controls failed as required. Challenge's six reference placeholders are not imported by Solution.

The [locked package](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/263a215acd295a260dec7a75ff6bebebb9789df9/linear-systems-and-elimination/IE-06/lean/lake-manifest.json) uses Lean **4.33.1**, mathlib [`0df444a360ea`](https://github.com/leanprover-community/mathlib4/commit/0df444a360eaa60ab8c11dca51a86af692955474), and LeanCert [`621a43d7cf21`](https://github.com/alerad/leancert/commit/621a43d7cf21f87872392a01e874f2f1dbddc926). [Reproduction instructions](lean/INFRASTRUCTURE.md) and the [verification summary](lean/verification/SUMMARY.md) distinguish the earlier local checks from the subsequent authoritative Linux run. The original target, permanent ID, and canonical path are unchanged.

The catalog reran the complete verification pipeline in [successful Linux CI run 37513136002](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/37513136002/job/112439363988), testing PR head [05b1c83e](https://github.com/ajt60gaibb/OpenProblemsInNLA/commit/05b1c83e11042d7067cd51c5a4bfc0265e7390f4) through merge revision [6091e87a](https://github.com/ajt60gaibb/OpenProblemsInNLA/commit/6091e87aa8538ea31df21fd06cce3d9e42f65c2a). The proof sources and checker configuration match the immutable proof linked above. The permanently retained [Linux receipt and logs](lean/verification/linux-ci-2026-10-06/README.md) record `comparator-accepted`: the actual non-root sandbox, six-target Comparator CLI/exporter, Lean default-kernel replay, and admitted-proof/native-execution rejection controls all passed. This is execution evidence from the catalog's own CI, independently reviewed alongside the original-target correspondence; it is not a claim of external human peer review.

## Scope of the resolution

For every $`\alpha>0`$, Urschel's Theorem 1.4 gives constants $`C_\alpha,n_\alpha`$ such that, for $`n\ge n_\alpha`$,

```math
\Pr\!\left\{\mathrm{growth}(\Pi(G_n))>
\sqrt n\,e^{C_\alpha\sqrt{\log n}}\right\}< n^{-\alpha}.
```

Here $`\Pi`$ applies partial pivoting and the paper defines $`\mathrm{growth}`$ using $`L`$ and $`U`$. [Section 5.1](https://arxiv.org/html/2610.06785v1#S5.SS1) and the [proof of Proposition 5.1](https://arxiv.org/html/2610.06785v1#S5.SS2) explicitly control every Schur-complement entry. Since $`\|G_n\|_{\max}\ge1`$ except with exponentially small probability, that argument also bounds the retained $`\rho_{\mathrm{PP}}`$ at the same scale. For each fixed $`\eta>0`$, $`e^{C_\alpha\sqrt{\log n}}=o(n^\eta)`$, implying the displayed limit. The Gaussian model and exact-arithmetic assumptions agree; pivot ties have probability zero.

Lloyd N. Trefethen's [*Instability of Gaussian elimination is exponentially rare (proof of partial result)*](https://arxiv.org/abs/2610.04761v1), posted 3 October 2026, treats the corner entry $`u_{nn}`$. In the correspondence supplied for this update, Trefethen dates that proof to 2015 and says he has not checked Urschel's proof. Credit for the conjecture remains with Trefethen, including its appearance in Trefethen and Bau's *Numerical Linear Algebra* (1997), p. 169; the full resolution is due to Urschel.

## References

John Urschel, [*On the Growth Factor of Random Matrices*](https://arxiv.org/abs/2610.06785v1), arXiv:2610.06785v1 (5 October 2026), Theorem 1.4, Section 5.1 and Proposition 5.1. Lloyd N. Trefethen, [*Instability of Gaussian elimination is exponentially rare (proof of partial result)*](https://arxiv.org/abs/2610.04761v1), arXiv:2610.04761v1 (3 October 2026). Lloyd N. Trefethen and David Bau III, *Numerical Linear Algebra*, SIAM (1997), p. 169.

Huang and Tikhomirov, [*Average-case analysis of the Gaussian elimination with partial pivoting*](https://doi.org/10.1007/s00440-024-01276-2), PTRF 189 (2024), 501–567, introduction, discussion of Edelman's numerical evidence and main theorems. Trefethen and Schreiber, [*Average-Case Stability of Gaussian Elimination*](https://doi.org/10.1137/0611023), SIAM J. Matrix Anal. Appl. 11 (1990), 335–360.

## Earlier status check — 2026-09-08

Searches for `Gaussian elimination n^{1/2} 2025 2026` and `site:arxiv.org Gaussian growth factor 2026` found polynomial upper bounds and the August worst-case results, but no proof at the square-root exponent. The distinction between exact and computed growth factors matters; the catalog statement fixes the former.

## Audit update — 2026-09-10

The [2024 journal article](https://link.springer.com/article/10.1007/s00440-024-01276-2) distinguishes its proved polynomial bound from the numerically suggested square-root scale. Searches for Gaussian GEPP growth and later work by Huang–Tikhomirov located no proof of the displayed exponent. A polynomial bound with an unspecified larger exponent does not resolve a parameter range of this sharper target.
