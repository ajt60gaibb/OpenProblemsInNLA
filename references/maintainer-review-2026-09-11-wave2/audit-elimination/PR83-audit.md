# Independent audit of PR #83: IE-15 rook growth

Frozen head: `b1a5d597a2d0a1b77f77ab8f98424b1328caebc2`.
Snapshot: `/private/tmp/nla-review-wave2-artifacts/pr-83`.
Primary submitted proof: `linear-systems-and-elimination/IE-15/solution.md` (380 lines). Line references below refer to this file. I read the full proof before consulting any supplied audit conclusion and independently recomputed the rational witnesses.

## Verdict

**PASS: the proof establishes the exact canonical values g_RP(3)=3 and g_RP(4)=14/3.** The bounds apply to real nonsingular inputs, every admissible rook path and tie choice, and the maximum of all active entries. Both sharp values are attained. No substantive mathematical error was found.

This is rigorous independent mathematical review, not a Lean/Coq certificate, external human peer review, or a novelty/priority determination. The source provenance remains as disclosed in the PR.

I compared the original canonical statement directly from `origin/main` in `/private/tmp/nla-review-wave2-20260911`. Its original ID, heading, mathematical statement and reference tail remain verbatim in the proposed entry. I also read [Higham's actual historical Problem 9.18, printed p. 193](https://pages.stat.wisc.edu/~bwu62/771/hingham2002.pdf), which asks for the small-order rook extrema and records numerical lower bounds only. The new analytic result matches the exact editorial catalog target. Its proof does not rely on any asymptotic growth theorem.

## 1. Reduction of arbitrary paths (lines 34–67)

An arbitrary successful rook path can be encoded by its eventual row and column order. Applying those permutations as a change of coordinates for the proof reproduces the same Schur complements up to permutations; it does not require any extra admissible operation in the original algorithm. Normalization by the original maximum absolute entry gives |A_ij|<=1.

The resulting factorization A=LDR has unit triangular L,R. Because the pivot dominates both its active column and its active row, every strictly lower L multiplier and strictly upper R multiplier has modulus at most one. Conversely these inequalities ensure the intended diagonal path is rook-admissible.

Let S be diagonal with the pivot signs. Then SA=(SLS)(SD)R, so multiplying those original rows by signs makes every pivot positive without changing multiplier moduli or growth. A simultaneous row/column sign change QAQ preserves these positive pivots and allows all final-row lower multipliers L_ni to be nonnegative, with each sign chosen independently.

Replacing A_nn by 1 is legitimate when bounding a positive final pivot: it changes none of the earlier pivot rows or columns, so leaves all earlier rook choices admissible. It increases the final Schur value by exactly 1-A_nn>=0 and preserves nonsingularity. This step cannot introduce an entry larger than the normalized original bound.

The bounds p_1<=1 and p_2<=1+p_1<=2 follow from the original A_22 entry. Every active entry after one and two updates has magnitude at most 1+p_1<=2 and 1+p_1+p_2<=4. This correctly includes entries that are not themselves pivots.

## 2. Order-three upper bound (lines 69–101)

With the proof's variables, the final pivot is `p_3=1+p c d+q e f`, where 0<p<=1, 0<q<=2, c,e in [0,1], and the remaining multipliers in [-1,1]. If p_3>3, then pcd>0 and qef>1, since pcd<=1 and qef<=2. Therefore d,f>0, qe>1 and qf>1.

The original-entry bounds on `A_23=-qf-pad` and `A_32=qe+pcb` force a<0 and b<0 respectively. But then `A_22=q+pab>q>1`, a contradiction. The earlier active entries are <=2, so this bounds the complete growth by three.

The extension to a possibly singular third-order matrix with the first two admissible nonzero pivots is sound. A zero final Schur value needs no estimate. For a nonzero value, a final-row sign change and the preceding proof bound its absolute value. This observation is needed and correctly used in the fourth-order argument.

## 3. Independent check of the two-pivot lemma (lines 103–224)

The lemma's h(c,d)=3cd+1+|c-d| is nonnegative on c in [0,1], d in [-1,1]. For d=-v<=0, it equals 1+c+v-3cv, whose extrema on the unit square are zero and two. For nonnegative d, positivity is immediate. Separate endpoint evaluation gives h<=4, h<=2+2c, and h<=2+2d for d>=0. On [0,1]^2, `|c-d|<=1-cd` gives h<=2+2cd.

If q<=1, the desired p h_1+q h_2<=8 is immediate. If q>1, `|q+pab|<=1` implies ab<0 and q<=1+p|ab|<=2. This leaves precisely the following cases, with no zero-sign branch omitted:

- b>0,a<0. The constraint `q c_2+p b c_1<=1` combines with h<=2+2c to bound the sum by `2[p+q+1+p(1-b)]<=4+4p<=8`, using q<=1+pb.
- a>0,b<0,d_2<=0. The bound is `4p+2q<=2+6p<=8`.
- a>0,b<0,d_2>0,d_1>=0. The constraint `q d_2+p a d_1<=1` and h<=2+2d yield the same argument with a in place of b.
- a>0,b<0,d_1=-v<0<d_2. Put c=c_1, B=-b, U=1+pBc and V=1+pav. The constraints give q c_2<=U and q d_2<=V, hence `q c_2 d_2<=min(q,U,V,UV/q)`.

In the last case, the function Phi(q,U,V)=2q+2min(q,U,V,UV/q) is indeed nondecreasing in all three positive arguments. For its q dependence, set u=min(U,V),w=max(U,V). The three formulas are 4q for q<=u, 2q+2u for u<=q<=w, and 2q+2UV/q for q>=w. The last derivative is nonnegative because q^2>=w^2>=UV, and the formulas agree at both joins.

Consequently q<=2,U<=1+c,V<=1+v and 0<=p h(c,-v)<=h(c,-v) permit replacing these variables by the stated upper bounds. Both 1+c and 1+v are <=2, so the minimum in Phi(2,1+c,1+v) is their product divided by two. The resulting exact expression is

    1+c+v-3cv + 4+(1+c)(1+v)
      = 8-2(1-c)(1-v) <= 8.

I also verified this last polynomial identity independently with symbolic arithmetic. Thus the lemma covers its complete domain, including negative d_i and all boundary values. It does not depend on a numerical optimizer or an unproved monotonicity assertion.

## 4. Order-four upper bound (lines 226–322)

Use c_i=L_4i>=0, d_i=-R_i4, w_i=p_i c_i d_i. Then p_4=1+w_1+w_2+w_3. The principal submatrix with indices 1,2,4 retains the same first two pivots and their row/column domination after deletion. Its final Schur value is 1+W, W=w_1+w_2. The preceding third-order absolute bound, including a zero final value, therefore gives W<=2.

If c_3=0 or d_3<=0, p_4<=3. Otherwise let C=c_3,D=d_3 in (0,1]. The original-entry inequalities on A_33, -A_34, A_43, multiplied by CD,C,D respectively, give the stated bound on 3w_3. These are valid one-sided consequences of the original absolute-value bounds, with nonnegative multipliers. Adding 3W yields `3(W+w_3)<=B(C,D)`.

The inner minimization is bilinear in u,v, so its minimum over [-1,1]^2 is attained at a corner. Its negative is the maximum of four separately affine functions of C,D. Thus B is separately convex even though it need not be jointly convex. Applying the endpoint inequality first in one coordinate and then in the other validly bounds it by its four corner values.

The three elementary corners are <=6,10,10 from W<=2 and p_1+p_2<=3. At (1,1), direct comparison of all four sign choices gives

    min_(|u|,|v|<=1)(uv+du+cv) = -1-|c-d|

for 0<=c<=1,-1<=d<=1. The same-sign corners are never smaller: depending on whether c>=d or c<=d, their differences reduce to nonnegative multiples of 1-c or 1-d. Therefore B(1,1)=3+p_1 h(c_1,d_1)+p_2 h(c_2,d_2)<=11.

The three hypotheses of the scalar lemma are exactly the absolute entry bounds on A_22, -A_24 and A_42 under the chosen signs. No extra positivity or symmetry assumption has been silently imposed. It follows that `p_4<=1+11/3=14/3`. The earlier active maxima <=1,2,4 are strictly below 14/3, establishing the entire path's growth estimate.

## 5. Exact attainment (lines 324–367)

The displayed A_3 has diagonal path pivots (1,1,3), determinant 3, and active matrices as printed. Each pivot dominates its active row and column, allowing ties. Its initial maximum is one and growth is three.

The displayed A_4 has pivots (1,1,5/3,14/3), determinant 70/9, and both printed intermediate matrices agree with independent rational elimination. The third pivot is tied for the maximum in its row and column, which is explicitly allowed. Its initial maximum is one and attained growth is 14/3.

I read the standard-library `verify_witnesses.py` before running it and obtained a full PASS. Independently, the SymPy elimination routine in `audit-elimination/independent_checks.py` recomputes the pivot conditions, determinants and growth values from the original matrices. Its report is `independent-check-results.json`. These checks support the lower bounds; the universal upper bounds rest on the derivations above.

## PDFs and reconciliation with PR #78

I rendered and visually inspected every page of the seven-page final proof PDF and two-page canonical PDF, alongside all PR #78 final documents. The theorem, sign reductions, scalar lemma, case split, corner argument, witnesses and references all appear. No clipping, overlapping equations, unreadable missing-glyph block, or substantive source/PDF inconsistency was found. The final proof page contains only the remaining references, a cosmetic pagination choice. PDF text and the complete page inventory are retained in `audit-elimination/pdf-qa/`.

PR #78's rook material proves only `g_RP(5)>=893/131` at t=1/6. I independently checked that witness and all five rook pivot conditions. It does not compete with or weaken #83's sharp third-/fourth-order results. On integration:

1. Preserve the existing IE-15 ID, path and original question.
2. Use #83's Solved status and result as the current resolution.
3. Retain #78's order-five witness as a separately attributed supplementary lower bound, without suggesting order-five optimality.
4. Change #78's present-tense “IE-15 remains Open” sentence to historical wording wherever imported into current resolution prose, and regenerate combined indexes/canonical PDF as required.

No additional mathematical condition is needed for acceptance at these frozen heads.


Archival note: local snapshot and runtime paths identify the audit environment. This published record includes review prose, independent check sources and JSON results; transient PDF page images, build trees and copied contributor inputs remain in the local audit archive. The original submissions are identified by the frozen Git commits above.
