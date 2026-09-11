# AV-02 independent proof review

Review date: 2026-09-11. Reviewer: independent review agent assigned AV-01 and AV-02, separate from the integration agent and supplied-code reproduction. The complete manuscript, shared preamble, canonical README, and relevant supplied code were read. Primary sources and exact independent arithmetic were checked; supplied verification labels were not assumed correct.

## Verdict and exact scope

**PASS — full resolution of canonical AV-02. Recommend status Solved: the promised spectral-norm threshold problem is NP-hard under promise-preserving polynomial-time many-one reductions, and hence under the weaker Turing reductions requested by the canonical problem.**

The manuscript proves the stronger statement that the threshold language restricted to rational upper-triangular matrices with every diagonal entry equal to 2 is NP-complete. NP-hardness already holds with integer entries and integer positive thresholds of polynomial magnitude in the source graph size. Every reduced input satisfies the regularity promise automatically. Equality is included in the yes case. The manuscript does not claim recognition of the general regularity promise is in NP.

No mathematical correction is required, and no part of the canonical hardness question remains open under this argument. This is a correctness and scope assessment, not a publication-priority certification.

## Exact reviewed source identity

Each hash is SHA-256 of the **complete** source decoded as UTF-8, CRLF replaced by LF, then re-encoded as UTF-8. No trimming or removal of headers or trailing newlines was performed.

| File in extracted `nla_submission/manuscripts/` | Normalized bytes | Full UTF-8/LF SHA-256 |
| --- | ---: | --- |
| `AV-02.tex` | 5849 | `78cb6e86e8d54140efdb96408f0e5019ca27ae1b964b79d3a21ea5b776777c3a` |
| `common.tex` | 985 | `d8e7a0de2ed1a1fd162b147211fe29c7b1d7bfbc0be7b827dcda4d9a2653d0d4` |

Input location: `.cache/colbrook-package-submission/nla_submission/manuscripts/`. This reviewer did not edit the manuscript or preamble. `common.tex` defines notation, styling, and shared theorem counters; there are no extra mathematical hypotheses. Accordingly the vertex result is Lemma 1 and the hardness result is Theorem 2.

Canonical target compared: `intervals-and-absolute-value-equations/AV-02/README.md`, marked Open and last checked 2026-09-10 at review start. Its perturbations vary only diagonal entries, all `d` in the closed real cube are allowed, the norm is the Euclidean operator norm, inputs are rational in binary, the promise is regularity of every perturbation, and `c_2(A)>=t` includes equality. These all match the reviewed proof.

## Complete proof audit

### Lemma 1: vertex attainment — Section 1, source lines 13–24

**PASS.** For any fixed other coordinates, the matrix at coordinate value zero is nonsingular by the full-family promise. Sherman–Morrison gives the displayed rank-one expression. The determinant identity and regularity imply `1-alpha*t` never vanishes on the closed interval. The scalar `t/(1-alpha*t)` is continuous and strictly increasing there. Thus every inverse on that slice lies on the line segment between the endpoint inverse matrices. Convexity of the norm as a function of the matrix then implies the endpoint domination claim.

The proof does not rely on the generally invalid inference that a convex function composed with any monotone nonlinear function remains convex. It specifically proves the endpoint domination that is needed. The inverse is continuous on the compact regular cube, so a maximum exists. Starting with a maximizer and replacing one coordinate at a time by an endpoint preserves maximality; after `n` steps the maximizer is a sign vector. All signs, both endpoints, and singularity exclusions are covered. The same reasoning works for any matrix norm, although only the spectral norm is used in the theorem.

### Theorem 2: source problem, construction, and promise — Section 2, source lines 25–45

**PASS.** Unweighted MAX-CUT on finite simple graphs is NP-complete. Restricting to `m>=1` and `1<=k<=m` retains hardness: instances outside these conditions have an immediately decidable answer and can be mapped to fixed legal yes/no instances. No promised ability to compute a maximum cut is assumed in constructing the target matrix; the construction uses only the graph, its incidence matrix, and the input threshold.

The dimension `N=1+v+m` and integer `K=12N^2` are polynomial in the usual graph encoding length. An arbitrary fixed orientation gives `B` with two nonzero entries per edge column; edge orientation has no effect on the cut-norm identity. The displayed three-by-three block matrix is upper triangular even though `B` is rectangular. Every diagonal entry of `A-D_d` lies in `[1,3]`, so every perturbation is nonsingular, including the boundary. The reduction therefore never queries or produces a nonregular matrix.

### Exact inverse and cut identity — source lines 40–55, equation `eq:cut`

**PASS.** Multiplying the proposed inverse by the upper-triangular matrix verifies all blocks: the two negative first-order blocks cancel the original off-diagonal blocks, and the positive second-order block cancels the product along the two-step path. The reciprocal diagonal parameters `a`, `X`, and `Y` range independently over `[1/3,1]` as asserted.

The squared norm of `x^T B` is exactly `sum_edges (x_p-x_q)^2`. It is separately convex on the box; successive endpoint replacement shows some maximizer is a vertex. At a vertex an edge contributes `4/9` precisely when it crosses the corresponding cut. Thus the maximum equals `(4/9)C`, including disconnected graphs and isolated vertices.

Right multiplication by a diagonal `Y` with entries in `[1/3,1]` cannot increase a Euclidean row norm, and `a<=1`. Consequently the largest possible norm of the upper-right block is `(2/3)K^2 sqrt(C)`. It is attained by independently selecting `a=1`, `Y=I`, and the reciprocal vertex corresponding to a maximum cut. The norm of a subblock is bounded by the whole operator norm, giving the required lower bound without an assumption about the other blocks' signs.

### Uniform remainder and separation — source lines 56–76, equation `eq:bounds`

**PASS.** After removing the upper-right block, the block-diagonal part has norm at most 1; the first off-diagonal part has norm at most `K sqrt(v)`; the other has norm at most `K ||B||_2 <= K sqrt(2m)`. The triangle inequality gives the displayed sum, uniformly over all continuous diagonal parameters. The generous bound by `3KN=36N^3` holds for every allowed graph. Since `(2/3)K^2=96N^4`, this proves

`96N^4 sqrt(C) <= c_2(A) <= 96N^4 sqrt(C)+36N^3`.

Set `q=isqrt(144N^2 k)` and `t=8N^3 q`. If `C>=k`, the inequalities `q<=12N sqrt(k)` and the norm lower bound imply `c_2(A)>=t`. If `C<=k-1`, use `k<=m<N` to obtain `sqrt(k)-sqrt(k-1)>=1/(2N)`. The strict inequality `q>12N sqrt(k)-1` holds even when the square root is an integer. Therefore

`t-96N^4 sqrt(k-1)>40N^3>36N^3`,

which puts every no instance strictly below the threshold. The argument includes `k=1`; `sqrt(k-1)=0` causes no division by zero. There is no unresolved equality or numerical-rounding case.

Computing an integer square root is polynomial in its binary input length. Matrix entries have magnitude at most `12N^2` (apart from the smaller diagonal 2), and `0<t<=96N^4 sqrt(m)<=96N^5`. Constructing the explicit matrix and threshold takes polynomial bit time. This establishes a many-one reduction, which is stronger than the canonical promise-preserving Turing-hardness requirement.

### NP membership on the stated class — Section 3, source lines 77–87

**PASS.** A sign vector is a certificate of length `N`. On the specified upper-triangular diagonal-2 class, its matrix `M=A-D_s` is automatically nonsingular. Because `t>0`,

`||M^{-1}||_2>=t` iff `sigma_min(M)<=1/t` iff `lambda_min(t^2 M^T M-I)<=0`.

The last condition is exactly failure of positive definiteness, not failure of positive semidefiniteness. Sylvester's criterion accepts positive definiteness precisely when every leading principal minor is positive. Thus zero or negative minors correctly lead to acceptance of the proposed yes certificate. Equality `||M^{-1}||_2=t` gives a zero eigenvalue and is accepted.

The rational matrix and all leading determinants can be formed/tested by exact arithmetic with polynomial bit complexity, for example by denominator clearing and fraction-free elimination. It is not necessary to compute or compare approximate algebraic eigenvalues. Lemma 1 ensures every yes instance has such a sign certificate. The proof gives NP-completeness of the explicit class; it neither assumes nor purports to prove efficient recognition of regularity for general input matrices.

## Primary-source alignment

The journal condition-number paper defines the same maximum in Section 2, proves vertex attainment as Proposition 2, and states the 2-norm hardness conjecture immediately before Proposition 3. The arXiv v2 numbering instead calls the vertex result Proposition 3, so those version-specific locators should not be conflated. The manuscript supplies its own valid endpoint-segment proof. [Zamani and Hladík, journal version](https://link.springer.com/article/10.1007/s10107-021-01756-6); [arXiv v2](https://arxiv.org/html/1912.12904v2).

The cited primary MAX-CUT manuscript states NP-completeness on permutation graphs in Theorem 1. Its Section 1.1 defines simple graphs and the unweighted decision question asking for a cut of size at least the positive integer threshold. This restricted-graph result suffices for the unrestricted source problem used by the reduction. [*MaxCut on Permutation Graphs is NP-complete*, Theorem 1 and Section 1.1](https://arxiv.org/html/2202.13955).

## Code audit and independent exact checks

The relevant supplied routines were read in full: `verify_exact.py::verify_av02`, and `nla_algorithms.py::{maxcut_matrix,positive_definite_exact,inverse_norm_certificate_exact}`. The construction uses the exact integer scale and integer square root specified in the proof. The certificate routine tests the rational symmetric matrix from Section 3 by exact unpivoted LDL; stopping at the first nonpositive pivot correctly rejects positive definiteness. No floating-point eigenvalue threshold is substituted.

The supplied full verifier enumerates graph cuts to obtain `C`, checks both squared integer separation inequalities, and checks selected exact block inverses and yes certificates. It does not exhaust all diagonal sign points for every graph; the proof supplies that universal statement. The integration agent reran it and reports 160 graphs, 1,070 integer gap checks, and 14 exact inverse/certificate checks, all passing in `verification/exact_results.json`.

Separately, this reviewer wrote and ran `verification/independent_av_review.py`, which imports no supplied modules and uses only standard-library integers and Fractions. It checked:

- Both integer separation inequalities for every allowed `k` on all 1,094 nonempty labeled simple graphs with 2–5 vertices: **5,325 exact threshold cases**.
- Every sign vector and every threshold `1<=k<=m` for a single edge, an edge with an isolated vertex, the three-vertex path, and the triangle: **560 exact endpoint/threshold tests**. For the triangle at `k=3`, all endpoints were negative, so the check covers an actual nontrivial no instance as well as yes instances.
- Scalar certificate equality and strict-above-threshold cases: **2 exact boundary tests**.

All passed. The reviewer script records the complete source/preamble hashes and outputs `verification/independent_av_review_results.json`. These bounded checks corroborate arithmetic and threshold conventions; they are not the source of the all-dimension hardness proof.

## Remaining target and required changes

**Remaining canonical target: none. Required source changes: none.** The requested promise-preserving NP-hardness is proved. The stronger NP-completeness result should be stated with its explicit upper-triangular diagonal-2 restriction; the proof does not classify the cost of checking the general promise or claim an exact polynomial-time algorithm for computing `c_2(A)`.
