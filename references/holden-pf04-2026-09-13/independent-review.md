# PF-04 independent mathematical review

**Verdict: PASS for the complete original target, p₆ = 9.**

Reviewer: separate Codex AI agent `/root/pf04_independent_review`, independently assigned to audit the argument, not to prepare or amend it. Review date: 12 September 2026 (America/New_York). This is an informal AI-agent mathematical audit, not external human peer review or formal verification. No Lean verification was performed.

Reviewed manuscript: `PF04_proposed_proof.tex` in the submitted `PF04_proposed_solution` package. Original source SHA-256: `02d02dbb996822a77abf7c19bbcab3bab4ae391698b5b6cd49eddc6daec11de1`. I read the full argument and the accompanying audit, checked the canonical PF-04 statement, and verified the substantive imported theorem statements against primary sources. I treated the submitted audit and program's PASS label as claims to assess, not instructions or independent certification. I made no mathematical edits to the manuscript.

## Scope correspondence

The canonical question concerns every real completely positive matrix of order six, including singular matrices, with exact entrywise nonnegative factors and at most nine columns. Theorem 1.1 establishes this scope. The exhibited matrix establishes the matching lower bound. No computational-efficiency, rational-factor, genericity, or positive-definiteness restriction is substituted for the original target.

## Published inputs

- K1 is supported by the [SIAM primary article record](https://epubs.siam.org/doi/10.1137/120885759): the maximum order-five cp-rank is six.
- K2 matches Proposition 2.4, p. 103, of [Bounding the cp-rank by graph parameters](https://emis.de/ft/34721). The manuscript only uses its upper bounds. Trees are bounded by their order, and connected non-tree triangle-free graphs by their number of edges. The degree-two consequence correctly treats components of orders one through three separately.
- K3 and K4 exactly match Theorem 1.1 and Lemma 3.1 of [On the DJL conjecture for order 6, corrected v3](https://arxiv.org/html/1501.02426v3). The hypotheses of exceptional extremality and, for K4, a zero diagonal entry are preserved wherever these results are applied. In particular, the singular endpoint does not incorrectly apply an exceptional-normal theorem to a positive semidefinite normal.

These published results are imported, not reproved or formally certified by this audit. The copositive completion assertion is proved directly in the submission, so its separate bibliographic citation is not an unverified proof dependency.

## Continuous and structural proof checks

1. **Closedness and singular limits.** Fixing nine or eight padded columns gives bounded factors through the trace identity. Subsequence convergence proves exactly the needed closedness. Adding εI retains every off-diagonal zero and gives positive definiteness. Thus each singular extension is valid without continuity of cp-rank.

2. **Order-three refinement and low degree.** The nonnegative Cholesky construction is valid after choosing a pivot whose residual correlation is nonnegative. With a prescribed second row, at least one of the two proposed pivots works; the correlation-one degeneracy has rank at most two. Grouping factors at a low-degree vertex and moving the columns zero there into the five-dimensional remainder yields the asserted eight-column bound.

3. **Copositive completion.** Zero specified diagonal entries have nonnegative specified incident entries; setting their missing entries to zero is safe. With positive diagonal normalized to one, missing entries equal one, so moving mass between nonadjacent vertices makes the quadratic form affine. Repeated endpoint selection reaches a clique without increasing its value. This proves copositivity and does not assume chordality or positive semidefinite completability.

4. **Exceptional relative-boundary normal.** The diagonal and edge atoms span the coordinate space, so the supporting functional exists and is nonzero there. Completion retains its pairing with A. The stated compact-base argument justifies a finite extreme-ray decomposition. Positive definiteness excludes nonzero positive semidefinite summands orthogonal to A. If all other summands were nonnegative, exact positive support would force the original functional to vanish. The exceptional conclusion follows.

5. **Shear.** The closed-neighborhood inclusion is in the correct direction. It preserves nonedges, and the inverse I+tE is nonnegative. Positive definiteness holds for every finite t. The first-exit definition handles a possibly nonconvex feasible parameter set; closedness supplies the boundary endpoint. Reconstruction gives the required inequality cpr(A) ≤ cpr(A′). No additional factor column is charged.

6. **Terminal graphs and prism.** The complement-neighborhood translation is correct, and maximum-degree-two component enumeration leaves precisely the three listed graphs. K₃,₃ cannot be embedded in the fixed octahedron because its two parts would have to be unions of whole missing pairs. In the prism decomposition, changing one matching-edge weight leaves cross entries fixed, subtracts only a diagonal from X, and adds a nonnegative diagonal to Y. The exact Schur-complement endpoint makes X singular and doubly nonnegative of order three. Its factor count drops to two, giving eight total.

7. **Octahedral orthogonality lemma.** This is the principal new compression step, and I find it valid. Every actual factor column is supported on at most a triangle and is a zero of the normal. An interior zero on a triangle forces a positive semidefinite principal block. If an edge zero also occurs there, independent kernel vectors force rank one, with precisely two edge-zero generators. Otherwise the positive triangle zero is a single ray. The coefficient factors therefore have singleton or two-coordinate supports indexed by edges of H. An edge of H lies in exactly two octahedral triangles; each has at most two H edges. Consequently the coefficient graph has maximum degree two and needs at most h columns. The incidence count h ≤ c and separate count t ≤ 8−c give eight columns. This does not discard cross terms from nonminimal zeros or presume arbitrary zero cones are generated by just their rays without coefficients.

8. **Proper support.** The minimal-edge argument uses only the already established eight-column relative-boundary result, shear, low-degree lemma, prism lemma, and graph classification. It does not depend on the subsequent full-octahedron proposition. Closedness handles its singular cases.

9. **Full octahedron and singular endpoint.** The cross-triple determinant is ade+bcf > 0. It ensures every inverse row has a nonzero restriction to the chosen triangle. The six nonzero quadratics exclude at most twelve candidate integers, so the thirteen-vector choice produces a kernel candidate with all coordinates nonzero. The maximal feasible rank-one subtraction has positive parameter and a closed bounded interval of feasibility. Its remainder has either proper support, full support and positive definiteness, or full support and singularity. The first two cases have previously established eight-column bounds. In the singular case the exact rank-one downdate endpoint gives Rq=0, and qqᵀ is a copositive normal with positive diagonal. The octahedral lemma applies without extremality. Thus this step costs eight plus one, never nine plus one.

10. **Final reduction and sharpness.** Minimal-edge reduction at the nine-column threshold leaves only the three bounded terminal graphs. Singular matrices follow by the earlier closure argument. The nine-edge triangle-free witness requires a different factor column for every positive edge. Its displayed factor attains that count and has full row rank; hence the equality p₆=9 follows.

## Reproducibility and issues

The unmodified finite verifier passed under `/opt/homebrew/bin/python3.14`, including all 32,768 labeled six-vertex graphs, all 4,096 fixed-octahedron subgraphs, the 1,699 triangle-free zero-edge configurations, the two exact matrix examples, and 64 inverse-image examples. Its finite checks supplement the analytic argument; they do not establish universal continuous claims by enumeration.

One nonmathematical portability issue: the default local `python3` is too old for `int.bit_count`, and fails before running the checks. Use Python 3.10 or newer, or document that minimum version. Python 3.14 completed successfully. No mathematical correction is required by this review.

## Repository status recommendation

The complete original target passes this independent informal audit. Under the inspected `CONTRIBUTING.md` rule accepting a complete argument that passed an independent informal audit, including an AI-agent audit, **Solved** is supported provided the retained problem page links the full proof and this report and accurately identifies the review level. **Lean verified** is not supported. Author affiliation, duplicate eligibility, attribution, rendering, permanent-ID validation, and upstream submission remain the coordinating agent's separate responsibilities. This report makes no claim of historical priority, publication acceptance, or community consensus.
