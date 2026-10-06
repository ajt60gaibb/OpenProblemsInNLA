# MI-18 — Bapat's q-permanent monotonicity conjecture

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex) · [Counterexample manuscript](solution.pdf) · [Manuscript source](solution.md) · [Order-four proof](proof.pdf) · [Audit](MI18_order4_audit_report.pdf) · [Reproducibility package](MI18_order4_audited.zip)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to specialist  
**Status:** Lean verified  
**Last checked:** 2026-10-06

**Rating rationale (historical):** Strict monotonicity on the whole PSD cone is a longstanding generalized-permanent barrier; its immediate impact is in specialist matrix-function inequalities.

## Negative resolution — 2026-10-06

**The arbitrary-order conjecture is false.** Kenta Kitamura reported a complete Lean disproof in [issue #329](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/329), using an ordered 144-row Gaussian-integer certificate. For some $`\varepsilon>0`$ the non-diagonal Hermitian positive definite matrix $`A=VV^*+\varepsilon I`$ satisfies

```math
-1\le q_1< q_2\le1,\qquad P_{q_2}(A)< P_{q_1}(A).
```

Positive definiteness implies positive semidefiniteness and strictly positive diagonal, so this is a counterexample to the exact original statement below. The proof first establishes $`P'_1(VV^*)<0`$, then preserves that sign under a sufficiently small positive diagonal perturbation. The perturbation size and comparison points are existential; neither the smallest counterexample order nor the real-symmetric case is settled here.

The [mathematical manuscript](solution.pdf) ([Markdown](solution.md), [standalone TeX](solution.tex)) gives the coefficient identities, ordered certificate and complete argument in conventional mathematical prose. This exposition was prepared by Codex from Kitamura's formalization; it is not an author-approved or human-authored manuscript. The formalization and supplied certificate are credited to Kitamura, whose source records AI assistance. No discovery-priority or external human-peer-review claim is made.

The [independent review record](../../reviews/2026-10-06-mi18-issue329/README.md) documents statement correspondence, source-hash and public-log checks, and an independent exact-integer recomputation with [a small local verifier](verify_certificate.py). The external Lean repository is linked at an immutable revision, rather than vendored here. The existing order-four and earlier special-case results remain valid.

## Computer-assisted order-four result — 2026-09-16

For every Hermitian PSD $`A\in\mathbb C^{4\times4}`$,

```math
P_q'(A)\ge0\qquad(-1\le q\le1).
```

Consequently, if $`A`$ is non-diagonal with positive diagonal, then $`q\mapsto P_q(A)`$ is strictly increasing on $`[-1,1]`$. This proves the complete order-four case of the displayed family. The later order-144 counterexample above disproves the arbitrary-order assertion without affecting this result.

The [proof](proof.pdf) uses rational Bernstein and contraction-square certificates. The [audited package](MI18_order4_audited.zip) contains the proof sources, exact certificate, original standard-library verifier, separately written SymPy verifier, recorded logs, manifests, and a literature-search record. The [original certificate package](MI18_order4_certificate.zip) is retained unchanged.

On 2026-09-17, this checkout reproduced the original verifier, the second implementation, all twelve deliberate corruption rejections, and the six-block tensor addendum using Python 3.13.2 and SymPy 1.14.0. Both package manifests passed. The two checkers use exact rational/symbolic arithmetic; they are not a Lean formalization.

The original argument and second verification path were produced by the same AI assistant. This is not independent human or external review, and it does not certify novelty or priority. The audit found no prior generic order-four theorem in the sources it examined, but its literature search is explicitly bounded.

## Problem statement

For a permutation $`\sigma\in S_n`$, let

```math
\mathop{\mathrm{inv}}\nolimits(\sigma)=
\#\{(i,j):1\le i< j\le n,\ \sigma(i)>\sigma(j)\}.
```

For real $`q`$ and $`A=(a_{ij})\in\mathbb C^{n\times n}`$, define

```math
P_q(A)=\sum_{\sigma\in S_n}q^{\mathop{\mathrm{inv}}\nolimits(\sigma)}
\prod_{i=1}^n a_{i,\sigma(i)},\qquad 0^0=1.
```

Is it true that, for every $`n\ge2`$, every non-diagonal Hermitian PSD matrix $`A`$ with $`a_{ii}>0`$ for all $`i`$, and every $`-1\le q_1< q_2\le1`$,

```math
P_{q_1}(A)< P_{q_2}(A)?
```

The expression is real for Hermitian $`A`$. The order of rows and columns in the inversion statistic is fixed.

## Relevance and ratings

 This polynomial interpolates $`\det A`$ at $`q=-1`$, the diagonal product at $`q=0`$, and $`\mathop{\mathrm{per}}\nolimits A`$ at $`q=1`$. The conjecture would compare a continuous family of matrix functions on the PSD cone, extending determinant/permanent inequalities. The non-diagonal and positive-diagonal hypotheses remove constant-polynomial cases.

## Lean proof and verification evidence

The reviewed proof is Kitamura's [external source at revision `4200da4`](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/tree/4200da4fc1a132d69c23fb877795b5b72089544b). The main project uses **Lean 4.33.1**, Formal Conjectures revision `89294ea02bd7cd678d59984add52cb4baef3dbf4`, and mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`; the [committed manifest](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/4200da4fc1a132d69c23fb877795b5b72089544b/lean/lake-manifest.json) pins the remaining dependencies.

The following unconditional declarations in [Counterexample.lean](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/4200da4fc1a132d69c23fb877795b5b72089544b/lean/Bapat/Counterexample.lean) settle the target:

- `Bapat.gramWitness_endpoint_negative` proves the negative endpoint derivative.
- `Bapat.exists_positive_definite_counterexample` gives an admissible order-144 counterexample.
- `Bapat.exists_decreasing_pair` gives a strict decreasing pair in the original interval.
- `Bapat.not_bapatMonotonicity` negates the universal assertion.

The declaration `BapatLal.qPermanentMonotonicity` in [Main.lean](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/4200da4fc1a132d69c23fb877795b5b72089544b/lean/Bapat/Main.lean) expresses the negative answer in the Formal Conjectures statement format.

The definition of the inversion count agrees with the original fixed ordering after the order-preserving relabelling from $`0,\ldots,143`$ to $`1,\ldots,144`$. `Bapat.complexQPermanent_eq_real` in [PermutationReality.lean](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/4200da4fc1a132d69c23fb877795b5b72089544b/lean/Bapat/PermutationReality.lean) proves that the real-part formulation equals the complex q-permanent on Hermitian matrices. Mathlib's `Matrix.PosDef` includes Hermitian symmetry and implies both PSD and positive diagonal. No extra premise is assumed to obtain the counterexample.

The author's [dated verification record](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/4200da4fc1a132d69c23fb877795b5b72089544b/lean/evidence/build_results.json) and [complete log](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/4200da4fc1a132d69c23fb877795b5b72089544b/lean/evidence/build.log) report successful checks on **5 October 2026 UTC**, including the main proof, standalone edition and compiled statement comparison. Transitive axiom reports for the declarations above contain only `propext`, `Classical.choice` and `Quot.sound`. The separate registration stub contains `sorry`, but is outside the complete proof's import graph and is used only as a statement-comparison target.

**Review level:** on 6 October 2026, separate Codex agents reviewed the statement and public evidence, and checked all 22 recorded source hashes against the pinned files. This catalog reviewed the author's public verification record, which includes cached/replayed modules; it did **not** rerun Lean locally. The independent Python computation checks the finite certificate, not the Lean kernel. This is the external-evidence route permitted by the [contribution rules](../../CONTRIBUTING.md#lean-verification). [Reproduction commands and detailed limitations](../../reviews/2026-10-06-mi18-issue329/README.md) are retained with the review.

## References

- R. B. Bapat and A. K. Lal, *Inequalities for the q-permanent*, Linear Algebra and its Applications 197–198 (1994), 397–409, monotonicity conjecture ([original paper](https://doi.org/10.1016/0024-3795(94)90497-9)).
- L. Mitchell, *A note on Bapat's q-permanent conjecture*, Operators and Matrices 14 (2020), 915–919, unnumbered Conjecture on p.917 and Theorems 1–3 ([primary paper](https://files.ele-math.com/articles/oam-14-56.pdf)).
- C. M. da Fonseca, *The $`\mu`$-permanent revisited* (2018), §4, related conjectures and corrections concerning ordered graph cases ([primary manuscript](https://arxiv.org/pdf/1804.02231)).

- K. Kitamura, *A Lean disproof of the Bapat–Lal q-permanent monotonicity conjecture* (2026), [immutable proof and certificate](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/tree/4200da4fc1a132d69c23fb877795b5b72089544b), reported in [issue #329](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/329).

## Historical status check — 2026-09-10

 Mitchell proves that the original positive-definite conjecture is equivalent to the displayed extension, and proves rank-one and order-three cases. Searches for “Bapat q-permanent conjecture”, “monotonicity”, “proof”, “counterexample”, and 2025–2026 found no resolution. The stronger proposed extension beyond $`[-1,1]`$ is not included; Mitchell explains why extending that assertion to all PSD matrices fails. No recent explicit reaffirmation of the exact conjecture was found.

**Literature audit:** Rechecked Mitchell’s PSD-extension conjecture and rank-one theorem, and searched for later q-permanent monotonicity resolutions. Rank-one and low-order cases are substantive parts of the displayed family; at that date, the general case still had only historical-source status evidence. This historical search is superseded by the negative resolution above.
