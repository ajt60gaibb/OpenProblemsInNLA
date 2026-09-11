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

### ✅ Five resolutions by Matthew J. Colbrook — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Each complete proof passed a separate Codex-agent audit against its exact catalog target on 11 September 2026. Three independent review agents covered the five proofs, with one review per proof. The original drafts were generated in a ChatGPT conversation; the independent agent verification is documented, and no external human peer review or formal proof certificate is asserted. The original statements and historical ratings remain intact. [Review reports, authorship and submission history](references/colbrook-2026-09-11/README.md).

#### IS-02 — negative resolution

[Original statement and resolution](eigenvalues-and-inverse-problems/IS-02/README.md) · [Complete manuscript](eigenvalues-and-inverse-problems/IS-02/solution.md) · [Manuscript PDF](eigenvalues-and-inverse-problems/IS-02/solution.pdf) · [Independent review](references/colbrook-2026-09-11/verification/reviews/IS-02-review.md). **Theorem IS-02, sections 1–2.** The order-four counterexample is real symmetric, nonnegative and stochastic, has spectrum $\{1,1,0,-1\}$ and positive trace, and is spectrally unique up to permutation. It lies outside every segment in the proposed locus, disproving the universal necessary condition at an allowed dimension.

#### SP-04 — negative resolution

[Original statement and resolution](eigenvalues-and-inverse-problems/SP-04/README.md) · [Complete manuscript](eigenvalues-and-inverse-problems/SP-04/solution.md) · [Manuscript PDF](eigenvalues-and-inverse-problems/SP-04/solution.pdf) · [Independent review](references/colbrook-2026-09-11/verification/reviews/SP-04-review.md). **Theorem SP-04, sections 1–4.** The stationary pair with uniquely smallest absolute multiplier fails to minimize the Frobenius distance on a nonempty open set of real $3\times3$ data matrices with distinct singular values in $(7/4,44/25)$. Both determinant signs are allowed, and the open-set argument refutes the algebraic-generic formulation.

#### SP-05 — affirmative resolution

[Original statement and resolution](eigenvalues-and-inverse-problems/SP-05/README.md) · [Complete manuscript](eigenvalues-and-inverse-problems/SP-05/solution.md) · [Manuscript PDF](eigenvalues-and-inverse-problems/SP-05/solution.pdf) · [Independent review](references/colbrook-2026-09-11/verification/reviews/SP-05-review.md). **Theorem SP-05, sections 1–3.** For arbitrary real symmetric positive definite $A,B$, a nonzero real positive-semidefinite eigenmatrix attains the smallest eigenvalue of $X\mapsto AXB+BXA$. Section 3 derives the exact symmetric/skew-symmetric Rayleigh-quotient inequality in the original target, without commutativity, rank restrictions or a simple-eigenvalue assumption.

#### KE-04 — affirmative resolution

[Original statement and resolution](eigenvalues-and-inverse-problems/KE-04/README.md) · [Complete manuscript](eigenvalues-and-inverse-problems/KE-04/solution.md) · [Manuscript PDF](eigenvalues-and-inverse-problems/KE-04/solution.pdf) · [Independent review](references/colbrook-2026-09-11/verification/reviews/KE-04-review.md). **Theorem KE-04, sections 1–3.** Strict interval occupancy holds for every allowed pair of block Lanczos iterations and every indicated index, in exact arithmetic before the first loss of full block dimension. The quadratic-polynomial argument includes multiplicities and excludes coincident interval endpoints in the stated range.

#### KE-03 — affirmative resolution

[Original statement and resolution](eigenvalues-and-inverse-problems/KE-03/README.md) · [Complete manuscript](eigenvalues-and-inverse-problems/KE-03/solution.md) · [Manuscript PDF](eigenvalues-and-inverse-problems/KE-03/solution.pdf) · [Independent review](references/colbrook-2026-09-11/verification/reviews/KE-03-review.md). **Theorem KE-03, sections 1–5.** The algorithm uses $O(\varepsilon^{-2}[1+\log(nK)])$ exact matrix-vector queries, with success probability at least $0.997$, for every input in the displayed model. It supplies both eigenvalue-location guarantees using the given condition bound $K$ and finite exact arithmetic between queries. The result bounds query count, not total runtime, bit complexity or floating-point error.

### ✅ Three further resolutions by Matthew J. Colbrook — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Separate Codex agents checked the complete arguments against the exact catalog targets and returned PASS. Two reviewers covered the three full resolutions; a third checked the related partial bound below. Original AI provenance is preserved, and the verification level is explicitly independent agent review. [Detailed reports and submission record](references/colbrook-additional-2026-09-11/README.md).

#### IS-03 — negative resolution

[Original statement](eigenvalues-and-inverse-problems/IS-03/README.md) · [Complete manuscript](eigenvalues-and-inverse-problems/IS-03/solution.md) · [PDF](eigenvalues-and-inverse-problems/IS-03/solution.pdf) · [Independent PASS report](references/colbrook-additional-2026-09-11/verification/reviews/IS-03-review.md). **Theorem 1 and equations (1)–(7).** The nonnegative real order-seven matrix $A=\operatorname{diag}(1/2,C_2,C_4)$ has a normalized characteristic-polynomial derivative whose seventh power sum is $-8593/823543<0$. Every power of a nonnegative matrix has nonnegative trace, so the derivative cannot be realized at order six, or after any zero padding. Reducibility and positive trace are allowed in the original target. This refutes its universal assertion.

#### SP-06 — negative resolution

[Original statement](eigenvalues-and-inverse-problems/SP-06/README.md) · [Complete manuscript](eigenvalues-and-inverse-problems/SP-06/solution.md) · [PDF](eigenvalues-and-inverse-problems/SP-06/solution.pdf) · [Independent PASS report](references/colbrook-additional-2026-09-11/verification/reviews/SP-06-review.md). **Theorem 1 and equations (1)–(8).** The integer-coefficient Laurent polynomial in Theorem 1 is real on a rigorously constructed star-shaped Jordan curve enclosing zero, while its $2\times2$ Toeplitz section has eigenvalues $-128\pm8i$. The proof checks continuity, injectivity and reality on the entire curve. It refutes the conjectured implication for every finite section; it does not refute the distinct limiting-spectrum statement.

#### IE-08 — affirmative resolution

[Original statement](eigenvalues-and-inverse-problems/IE-08/README.md) · [Complete manuscript](eigenvalues-and-inverse-problems/IE-08/solution.md) · [PDF](eigenvalues-and-inverse-problems/IE-08/solution.pdf) · [Independent PASS report](references/colbrook-additional-2026-09-11/verification/reviews/IE-08-review.md). **Theorem 1, Lemmas 2–12 and the final four proof sections.** The end-to-end algorithm uses $O(n^3\log^c(n/\delta))$ arithmetic operations and $O(\log(n/\delta))$ mantissa bits, with universal constants, for every complex input with $\|A\|_2\le1$. With probability at least $0.99$ it returns an exactly upper triangular $T$ and a $Q$ satisfying both displayed residual bounds. The proof includes finite random sampling, deterministic work caps, global recursive conditioning and floating-point error control, without an input separation or diagonalizability assumption. It is an asymptotic existence result with conservative constants, not a production implementation.

**Related partial result — IS-05 (still counted as open).** [Theorems 1–2](eigenvalues-and-inverse-problems/IS-05/solution.md), independently checked in a [separate PASS report](references/colbrook-additional-2026-09-11/verification/reviews/IS-05-review.md), prove the upper bound $\alpha_*\le1/2$ and an additional parity obstruction. The updated interval is $17/92\le\alpha_*\le1/2$; its exact value remains unresolved. [IS-05](eigenvalues-and-inverse-problems/IS-05/README.md) is **Partially resolved**, not Solved.

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
claim that an unrefereed proof is incorrect. The records below were checked
on **2026-09-10**.

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
