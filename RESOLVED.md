# Solved problems and solution claims

[Open catalog](CATALOG.md) · [Status definitions](README.md#problem-status) · [Report a solution](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/new?template=correction_or_resolution.md)

**Solved problems stay visible.** Their IDs and original statements are retained,
with a prominent status, the resolution reference, its date and exact scope.
They do not contribute to the open count. A counterexample is a solution to a
conjecture's truth question; it is recorded as a negative resolution.

**✅ SOLVED** means the exact target has a published or independently verified
resolution. **🟠 SOLUTION CLAIMED** means a primary manuscript reports a full
resolution whose proof has not been independently verified here. Neither status
is counted as open. A partial result leaves the surviving target in the open
catalog with **🟡 PARTIAL** and an explanation of what remains.

## Resolved catalog entries

### ✅ MI-13 — Nobori's spectral-middle-factor commutator inequality

[Original statement and complete proof](matrix-inequalities-and-norms/MI-13/README.md) · [PDF](matrix-inequalities-and-norms/MI-13/problem.pdf)

**Affirmative resolution recorded 2026-09-10.** The complex refined commutator
bound in [Audenaert, Corollary 5](https://arxiv.org/pdf/0907.3913), combined with
square padding and a two-unitary decomposition of a contraction, proves the
exact target for every allowed rectangular dimension. The constant is sharp.
The complete repository proof passed two independent Codex-agent reviews of
its assumptions and steps. It has not received external peer review or Lean
formalization; no novelty claim is made. The former difficulty label remains
historical and the entry no longer contributes to the open count.

### Five factorization resolutions by Matthew J. Colbrook — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Three separate Codex agents reviewed all seven arguments; five resolve full canonical targets and two provide partial family results. This is independent agent verification, not external peer review or formal certification. [Submission record and reproduction](references/colbrook-factorization-2026-09-11/README.md).

**NM-03 (Solved).** The exact rational-input decision problem is NP-hard under polynomial-time many-one reductions, even for strictly positive symmetric positive-definite inputs. The proof supplies an inverse-polynomial additive squared-error gap and a polynomial-time rational perturbation to simple spectrum. Factors may be real, exactly as in the canonical question. NP membership and constant-relative-error hardness are not asserted.  [Complete proof](references/colbrook-factorization-2026-09-11/manuscripts/NM-03_rank_two_approximation_hardness.pdf), Theorem 1; Theorem 5 and Corollary 6 strengthen the construction; [review](references/colbrook-factorization-2026-09-11/verification/reviews/NM-03-review.md).

**NM-04 (Solved).** The complete Rowland--Wu coefficient identity holds for every positive real rectangular matrix and all $m,n\ge1$. The proof identifies the coefficient sum with one determinant and constructs a null vector after scaling. Vanishing minors and the cases $m=1$ or $n=1$ are included. This proves the displayed coefficients, beyond the previously known algebraic-degree bound.  [Complete proof](references/colbrook-factorization-2026-09-11/manuscripts/NM-04_sinkhorn_identity.pdf), Theorem 1; [review](references/colbrook-factorization-2026-09-11/verification/reviews/NM-04-review.md).

**NR-04 (Solved).** The nine-point matrix $D_{ij}=(i-j)^2$ has nonnegative rank seven, so no exact six-term nonnegative factorization exists. A polygon-contact argument applied to both factors, together with Sylvester's rank inequality, proves the lower bound; an explicit seven-term integer factorization proves the upper bound.  [Complete proof](references/colbrook-factorization-2026-09-11/manuscripts/NR-04_nine_point_distance.pdf), Theorem 1, with Theorem 4 for the lower bound; [review](references/colbrook-factorization-2026-09-11/verification/reviews/NR-04-review.md).

**PF-02 (Solved).** A strictly positive integer $6\times6$ matrix has ordinary rank six and real positive semidefinite rank three, while its minimal-factor congruence quotient is disconnected. A continuous congruence-invariant orientation takes opposite signs on two explicit factorizations, proving actual disconnectedness in the required quotient topology. Further constructions cover every factor size $k\ge3$, including strictly positive rational examples by a nonquantitative perturbation argument.  [Complete proof](references/colbrook-factorization-2026-09-11/manuscripts/PF-02_disconnected_orbits.pdf), Theorem 1; Theorem 4 extends the counterexamples to every factor size; [review](references/colbrook-factorization-2026-09-11/verification/reviews/PF-02-review.md).

**PF-05 (Solved).** For every real size-two positive semidefinite factorization of an ordinary-rank-three matrix, feasible straight-line infinitesimal rigidity is equivalent to uniqueness up to congruence. The zero-entry argument handles repeated or singular factors and zero rows and columns; the cited positive-entry theorem covers the remaining case. The feasible directions and equivalence group agree exactly with the canonical definitions.  [Complete proof](references/colbrook-factorization-2026-09-11/manuscripts/PF-05_rigidity_with_zeros.pdf), Theorem 1, with Theorem 8 for the zero-entry construction; [review](references/colbrook-factorization-2026-09-11/verification/reviews/PF-05-review.md).

#### Related partial family results

**NR-03 (Partially resolved).** The fixed three-bit quadratic correlation matrix has nonnegative rank exactly eight. Its ordinary-rank-seven parity null vector constrains both factors in a hypothetical seven-term factorization; nine distinguished entries then exclude such a factorization. The full prescribed-completion conjecture for every $n\ge4$ remains unresolved. The parity restriction is proved only for a hypothetical factorization whose inner dimension equals ordinary rank; it is not imposed on arbitrary wider factorizations. [Complete proof](references/colbrook-factorization-2026-09-11/manuscripts/NR-03_n3_exact_rank.pdf), Theorem 1 and Lemma 2; [review](references/colbrook-factorization-2026-09-11/verification/reviews/NR-03-review.md).

**PF-01 (Partially resolved).** The real positive semidefinite rank is exactly four for $n=5$ and $n=6$. Explicit graph factors give the general bound $\operatorname{rank}_{\rm psd}M^{(n)}\le\lceil2\sqrt{2\lfloor(n-1)/2\rfloor}\rceil$, and submatrix monotonicity gives a lower bound of four for every $n\ge5$. The exact ranks as a function of $n$ remain undetermined for $n\ge7$. In particular, the new upper bound five at $n=7,8$ is not accompanied by a matching lower bound five. The finite orders remain part of this single family entry. [Complete proof](references/colbrook-factorization-2026-09-11/manuscripts/PF-01_subset_intersection.pdf), Theorem 1, Corollary 5 and equation (8); [review](references/colbrook-factorization-2026-09-11/verification/reviews/PF-01-review.md).

## Published resolutions of historical questions

These questions were screened out before receiving current catalog folders;
they are included here to make their resolutions easy to find. No new problem
IDs or admissions are created by this list. Sources and scope rechecked on
**2026-09-10**.

| Status | Historical question | Resolution and scope |
| --- | --- | --- |
| ✅ **SOLVED** | Higham's growth bound for complex symmetric matrices with positive-definite real and imaginary parts | S. W. Drury, *Fischer determinantal inequalities and Higham's Conjecture*, LAA 439 (2013), 3129–3133, [published result](https://doi.org/10.1016/j.laa.2013.08.031). The bound of two for elimination without pivoting answers the historical below-three question. [Zhang's 2026 paper, §1.1 and Appendix A](https://arxiv.org/html/2604.23024), explicitly traces and refines that result. This does not assert the same bound for arbitrary complex symmetric matrices. |
| ✅ **SOLVED** | Higham's Fréchet-derivative Jordan-form question, *Functions of Matrices*, Research Problem 3.11 | V. Noferini, *The Jordan canonical form of the Fréchet derivative of a matrix function and the bivariate Jordan problem*, [published online in 2026](https://doi.org/10.1016/j.laa.2026.06.002); [primary manuscript, §§4–5](https://arxiv.org/html/2512.08399). The matrix-function problem is answered; the more general bivariate Jordan problem has separate unresolved cases. The journal issue date is October 2026, later than the online publication. |

## Former catalog entries with complete-resolution claims

The classification below concerns the strength of the available evidence, not a
claim that an unrefereed proof is incorrect. Checked **2026-09-10**.

<a id="ie-01"></a>

### 🟠 IE-01 — Forsythe's conjecture beyond restart length two

[Original statement and resolution](linear-systems-and-elimination/IE-01/README.md) · [PDF](linear-systems-and-elimination/IE-01/problem.pdf)

Colbrook, Stepaniants and Townsend's [September 2026 preprint, v2, Theorem 1.1](https://arxiv.org/html/2609.04659v2), reports convergence for restart length three and counterexamples for every restart length at least four. This covers the entire former entry. Removed from the open count on September 8; the stable page is restored with the claim prominently displayed. The full proof has not been independently audited by this catalog.

<a id="tr-02"></a>

### 🟠 TR-02 — Greedy cross approximation of the fermionic kernel

The [current workshop report, update after Problem 4.2](https://arxiv.org/html/2602.05394), records V. S. Pendyala's [2026 full-solution claim](https://doi.org/10.5281/zenodo.21863274) for the logarithmic cutoff/accuracy rate. The workshop's report of the claim was checked; the claimed proof itself has not been independently reviewed. The [screening note](references/SCREENED-OUT.md#screened-items-that-are-not-counted) preserves the context.

<a id="re-04"></a>

### 🟠 RE-04 — Finite-family structured approximation with relative error

The [August 2026 update following the abstract of Amsel et al.](https://arxiv.org/html/2507.19290v2) reports an improvement to relative error $1+\varepsilon$ and links an author-endorsed argument. This supersedes its stale question in §5. The [screening note](references/SCREENED-OUT.md#excluded-and-uncounted-leads) records the exact distinction from the still-open linear-family and nonadaptive questions. This catalog has checked the scope of the reported resolution, not independently verified its proof.

### 🟠 Sharp Paulsen bound — proposed FR-12, not admitted

[Lau and Ramachandran, §7, manuscript p. 13](https://arxiv.org/pdf/2510.13751),
announce an optimal unrestricted distance bound in forthcoming work. Their
normalization differs by the frame energy from the usual Parseval formulation;
the announcement addresses the proposed sharp strengthening. The announcement
was independently checked, but its forthcoming proof was not available for
verification. The temporary expansion candidate was withheld and does not
contribute to the open count. Its disposition is recorded in the
[expansion screen](references/EXPANSION-TO-200-2026-09.md).

Other historical exclusions and full-proof claims remain documented in the
[source record](references/SOURCES.md#important-historical-questions-excluded).
This page highlights resolutions and former catalog IDs; it is not a list of
every rejected candidate.

## Recording a new resolution

1. Keep the original problem ID, folder and statement. Do not delete or reuse the ID.
2. Set `**Status:** Solved` or `**Status:** Solution claimed` on its canonical page. Add a prominent resolution notice, a primary reference and theorem/page locator, the resolution date, the outcome (affirmative, negative or classification), and a comparison with the original assumptions and quantifiers.
3. For a partial result, use `Partially resolved` and state the exact remaining cases. A weaker bound, a different algorithm, or a different input model does not settle the target.
4. Add the resolution here, regenerate the catalog indexes with `python3 tools/update_catalog.py`, and regenerate the affected TeX/PDF with `python3 tools/render_problems.py ID`.
5. Submit a pull request. An issue being closed is not, by itself, evidence that a mathematical problem is solved. If a claim is withdrawn or a gap is found, retain the history and revise the status using the new evidence.
