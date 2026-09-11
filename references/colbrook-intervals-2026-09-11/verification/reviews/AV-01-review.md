# AV-01 independent proof review

Review date: 2026-09-11. Reviewer: independent review agent assigned AV-01 and AV-02, separate from the integration agent and supplied-code reproduction. The complete manuscript, its complete shared preamble, the canonical README, and relevant supplied programs were read. Submitted verification labels were treated as claims, not evidence of correctness.

## Verdict and exact scope

**PASS — full resolution of canonical AV-01. Recommend status Solved, with the classification in deterministic polynomial time in the rational binary Turing model.**

Theorem 1 and Section 4 recognize exactly `2^n` distinct real solutions of `Ax+|x|=b` for every rational square `A`, rational `b`, and `n>=1`. There is no finiteness, nonsingularity, spectral-radius, or genericity promise. Infinite solution sets are negative instances. The result supplies a Boolean recognition algorithm, not an algorithm listing exponentially many solutions. No mathematical correction is required. No case of the canonical decision question remains open under the proved characterization.

This review establishes correctness and scope of the submitted argument; it does not independently establish publication priority.

## Exact reviewed source identity

Hashes are SHA-256 of the **complete** file decoded as UTF-8, with CRLF replaced by LF and re-encoded as UTF-8. No stripping, trimming, header removal, or newline removal was performed.

| File in extracted `nla_submission/manuscripts/` | Normalized bytes | Full UTF-8/LF SHA-256 |
| --- | ---: | --- |
| `AV-01.tex` | 7443 | `9a4765c26b64d8383872a0970a6752ec63e48020f5b0a4509ad49cf6047c524a` |
| `common.tex` | 985 | `d8e7a0de2ed1a1fd162b147211fe29c7b1d7bfbc0be7b827dcda4d9a2653d0d4` |

Input location: `.cache/colbrook-package-submission/nla_submission/manuscripts/`. No manuscript or preamble was edited by this reviewer. The preamble contains typography, theorem counters, and notation/link macros; it introduces no additional mathematical hypothesis. The theorem is numbered 1; the later remark shares the counter but does not change the theorem's scope.

Canonical target compared: `intervals-and-absolute-value-equations/AV-01/README.md`, the version marked Open and last checked 2026-09-10 at the start of this review. Its arbitrary rational inputs, all-real-solutions count, infinite-negative convention, and bit model agree with the manuscript.

## Complete proof audit

### Theorem 1, necessity — Sections 1–2, source lines 7–49

**PASS.** The closed-orthant solution set is an affine subspace intersected with linear inequalities, hence convex. A finite convex set contains at most one point. Each solution belongs to at least one closed orthant. At exactly `2^n` solutions, the number of solution/orthant incidences is both at least and at most `2^n`. Consequently every orthant has one solution and no solution lies on a coordinate hyperplane. This proves the strict sign assertion without a hidden general-position assumption.

If an orthant matrix `A+D_s` were singular, a nonzero null vector through its strictly interior solution would produce a sufficiently short nonconstant line segment within the same orthant. That would contradict finiteness. Multiplication on the right by `D_s` gives the nonsingular matrix `I+A D_s` and the strictly positive solution `u_s`.

The determinant `q(d)=det(I+A D_d)` is multiaffine because each column depends affinely on its own coordinate. Replacing column `i` by `b` gives a multiaffine `r_i` independent of `d_i`. Cramer's rule and positivity of `(u_s)_i` imply that the nonzero determinants at endpoints of every coordinate edge have equal signs. Connectivity of the cube gives one common sign. Multiaffine averaging at the center gives `average_s q(s)=q(0)=1`, so the common sign is positive. Every `r_i(s)` is then positive as well. Multiaffine interpolation is a convex combination of vertex values throughout the **closed** cube, including its boundary; both `q` and all `r_i` stay strictly positive. At the center `r_i(0)=b_i`, proving `b>0`.

The resulting `u(d)` is positive and continuous everywhere on the compact cube. For an arbitrary feasible `y`, the construction `d_i=y_i/u_i` when `u_i>0` is valid since `|y_i|<=u_i`; the case `u_i=0` forces `y_i=0` and is handled by `d_i=0`. Thus `y=D_d u`, and invertibility identifies `u` with `u(d)`, excluding that zero case after all. Conversely every `D_d u(d)` satisfies the paired inequalities. This proves equality of the feasible set with a continuous image of the compact cube, not merely inclusion. Boundedness and strict positivity throughout `P` follow.

### Theorem 1, sufficiency — Section 3, source lines 50–57

**PASS.** Because `b>0`, the origin strictly satisfies all inequalities, so `P` is nonempty and full dimensional, even when the matrix itself is singular. Both inequalities from one pair cannot be active simultaneously: they would force `y_i=u_i(y)=0`, contradicting the hypothesis. A vertex needs `n` independent active normals; with `n` pairs and at most one active inequality per pair, it has exactly one from each pair and those normals are independent. Its nonzero coordinates and active equations make it an AVE solution.

The coordinate-flipping edge argument is valid without assuming a simple-polytope theorem. After retaining `n-1` independent active equations, their common direction space is one-dimensional. The omitted normal is independent of them, so a direction strictly relaxing it exists. Every initially inactive inequality has positive slack; sufficiently short positive movement remains feasible. The feasible ray parameter set is a closed interval with a finite positive endpoint by boundedness. At that endpoint some previously inactive inequality must become active. It cannot be opposite a retained inequality, since the retained one is still active and simultaneous activity in a pair is forbidden. It cannot be the relaxed original inequality. The only remaining possibility is the opposite member of the omitted pair. Its value changes along the ray, so its normal is independent of the retained normals. The endpoint is indeed another vertex, changing exactly the chosen sign. This also covers `n=1`, where zero equations are retained.

A nonempty bounded full-dimensional polyhedron has a vertex. Connectivity by successive coordinate flips now supplies a vertex for every sign pattern. For each pattern its active system is nonsingular, hence determines at most one point. Every AVE solution lies in `P`, has strictly nonzero coordinates by the same slack condition, and solves one such nonsingular system. There are therefore exactly `2^n` solutions and no additional continuum or boundary solutions.

### Algorithm and bit complexity — Section 4, source lines 58–75

**PASS.** Rejecting `b_i<=0` is justified by necessity. Once `b>0`, `P` is known nonempty, so its unboundedness is equivalent to a nonzero recession direction. The recession inequalities imply `-Ar>=|r|`, hence `-1^TAr>=||r||_1>0` for every nonzero direction. Scaling to `-1^TAr=1` preserves the homogeneous inequalities. Conversely the normalization excludes zero. This proves the single recession-feasibility LP is exact, including unbounded sets containing lines or rays.

On `P`, all `u_i` are nonnegative. Thus failure of the pointwise condition `u_i>0` is exactly feasibility of the equality `A_{i,:}y=b_i` together with the original inequalities. This does not require an approximation to a strict inequality or a numerical positivity tolerance. The algorithm uses at most `n+1` exact rational feasibility problems, followed by Boolean decisions, and correctly stops early on rejected instances.

Each LP has `n` variables, `2n` inequalities, and one equality (or two additional inequalities). Forming `A±I` and summing the entries of each column for the normalization has polynomial rational encoding length; a common-denominator representation may enlarge lengths by a polynomial factor, never exponentially in the input length. Rational linear feasibility has deterministic polynomial bit complexity. There is no claim of strong polynomiality and no need to enumerate the `2^n` orthants in the recognition algorithm.

### Remark and explicit example — source lines 72–89

**PASS.** For scalar `A=2,b=1`, the feasible set is `(-infinity,1/3]`, its slack is at least `1/3`, and the only AVE solution is `1/3`. Thus positivity alone would not suffice; the boundedness check is essential.

Independent exact Fraction substitution verified all four displayed two-dimensional solutions. In displayed order, the determinants of their sign systems are `73/25,-7/25,-7/25,13/25`, all nonzero. Every orthant occurs once, and a nonsingular system permits no second solution within an orthant. The absolute matrix has identical rows `(3/5,3/5)`, so its spectral radius is exactly `6/5`; the example genuinely lies outside the earlier `rho(|A|)<1` subclass.

## Primary-source alignment

Hladík's journal paper explicitly leaves this Boolean maximum-count recognition question open in Section 2.3 and again in Section 7. Its different threshold result concerning more than `2^(n-1)` solutions is not the canonical target. The supplied theorem addresses the full exact-count question. The paper's Proposition 9 concerns the stated spectral-radius subclass. [Hladík, *Absolute value equations with 2^n solutions*, journal version](https://link.springer.com/article/10.1007/s11590-025-02251-z).

The cited Karmarkar paper's publisher abstract explicitly gives a polynomial bound in the input bit length, consistent with the standard exact rational LP complexity theorem used in Section 4. This review uses that standard theorem, not the floating-point program, for the complexity conclusion. Full subscription text was not needed for a new or specialized LP assertion. [Karmarkar, *A new polynomial-time algorithm for linear programming*](https://link.springer.com/article/10.1007/BF02579150).

## Code and reproduction audit

The full `code/verify_av01_exact.py` was inspected. Its Fraction Fourier–Motzkin elimination combines opposite-sign coefficient rows with positive multipliers, preserves zero-coefficient rows, and recognizes inconsistent constant inequalities. Positive rescaling and keeping the tightest identical normal preserve the feasible set. Equalities are encoded as two inequalities. The recognition function implements the manuscript's tests. Its independent orthant comparator returns true exactly when every sign matrix is nonsingular and its solution is strictly in that orthant, which is equivalent to the maximum finite count by the incidence argument above.

The file correctly states that Fourier–Motzkin is only a small-instance checker, not a polynomial-time LP implementation. `nla_algorithms.py::av01_recognize_float` was also inspected: its additional `[-1,1]` recession bounds are redundant under the normalization because `||r||_1<=1`, but the floating-point answers remain diagnostic rather than bit-model certificates.

The integration agent reran the supplied full exact suite; the regenerated `verification/AV-01_exact_results.json` was inspected and reports **1,046 passing exact instances** (45 scalar, 701 two-dimensional, 300 three-dimensional). The numerical suite is supplementary and is recorded separately. No general correctness claim is inferred from finite random tests.

The independent reviewer additionally wrote and ran `verification/independent_av_review.py`, using only Python's standard library and importing no submission code. Its exact rational substitution/determinant checks passed; it records the complete manuscript and preamble hashes in `independent_av_review_results.json`.

## Remaining target and required changes

**Remaining canonical target: none. Required source changes: none.** The general rational Boolean recognition question is in P. The supplied code is a reproduction/checking suite, not a delivered implementation of a polynomial-time exact LP solver; the canonical problem asks for the complexity classification, which the proof supplies.
