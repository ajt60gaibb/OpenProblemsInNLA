# PF-01 independent proof review

**Verdict: PASS for all stated mathematical results; PARTIAL coverage of canonical PF-01.** The real PSD ranks at n=5 and n=6 are four. The general upper bound and monotonicity argument are valid. The exact rank for n>=7 is not determined. These orders remain one catalog problem, not separate resolutions.

Reviewer: independent Codex subagent `/root/review_transfer_volume_learning`, 2026-09-11. This is an independent mathematical audit, not human peer review or a priority certification. The entire original TeX, including its definitions, proofs, extensions, scope, and bibliography, was read. No proof or canonical file was edited.

## Source identity and target

Original: `.cache/colbrook-all-submission/nla_submission/manuscripts/PF-01_subset_intersection.tex`.

Complete-source normalized UTF-8 byte count: **16890**. SHA-256: **`4ee1bf1535124dca3bf1d4325b1ebdafd51f76c6459b6be17cc8f0a0d0563940`**.

Normalization means replacing CRLF with LF and hashing the UTF-8 encoding of the entire text, without trimming or other changes. The source is standalone and has no external mathematical preamble.

Canonical comparison: `nonnegative-and-positive-factorizations/PF-01/README.md`. The target asks for real symmetric PSD rank of the subset-intersection family for every integer n>=5. Complementing each column subset is a permutation and changes its entries to `floor(n/2)-|I intersect K|` with both indices of size floor(n/2). This is exactly the manuscript's D for n=5 and its corresponding D for n=6. It does not change field, factor cone, or factor size.

The primary source separately poses the n=5 case as Problem 9.1 and the full family as Problem 9.2; it gives bounds 3 and 4 in the former case. [Fawzi et al., Section 9.1](https://arxiv.org/html/1407.4095)

## Theorem-by-theorem audit

### Theorem 1, label `thm:main`: n=5 has PSD rank four

**Upper bound.** The four Helmert vectors are orthonormal and span the sum-zero subspace of R^5. Incidence-vector differences lie in that subspace. Division by sqrt(2) therefore makes their squared distances `2-|I intersect K|`. Reshaping four coordinates into a 2-by-2 matrix preserves this norm. If `R_I=(Z_I; I_2)` and `S_K=(I_2; -Z_K^T)`, the trace of their PSD outer products is `||R_I^T S_K||_F^2=||Z_I-Z_K||_F^2`. All factors have the required real size four.

**Lemma 2, `lem:hessian`.** At `diag(alpha,beta,0)`, the quadratic determinant term is `(alpha h22+beta h11)h33-alpha h23^2-beta h13^2`. Its first product has rank at most two and its two squares contribute at most two more. When beta=0 the bound becomes three. This remains true for indefinite singular matrices, for rank zero, and after restriction to a linear five-dimensional pencil. Consequently every zero of any such determinant cubic has Hessian rank at most four, and every point whose pencil has rank at most one has Hessian rank at most three. The argument needs no positivity away from the ten factor points.

**Lemma 3, `lem:cubic`.** The two zero derivative equations at each pair give `b_ij=a_j-2a_i` for the coefficient of `x_i^2 x_j`. Subtracting `q(x) sum a_i x_i` eliminates all non-multiaffine monomials and preserves the outside-derivative equality. The graph of triples sharing a pair is connected, forcing the remaining coefficients all to equal lambda. This verifies the full six-parameter family, rather than merely checking selected examples.

The displayed Hessian determinant identity was checked independently by a structural reduction. For the pair {1,2}, let `s=a1+a2`, choose orthonormal pair sum/difference vectors, and choose the normalized all-ones vector and two perpendicular vectors on the other three coordinates. In these coordinates the pair-sum row has only one nonzero coupling, `sqrt(6)(lambda-4s)`, to the outside all-ones direction. Expanding the determinant along this row and its column leaves the pair-difference diagonal `4s` and the two outside perpendicular diagonals `4s-2lambda`. It gives

```text
-6(lambda-4s)^2 (4s)(4s-2lambda)^2
= -96s(2s-lambda)^2(4s-lambda)^2.
```

The other couplings drop out of this expansion. This proves the identity for unspecialized real parameters, including vanishing factors, without relying on the submitted symbolic diagnostic.

**Reduction from arbitrary size-three factors.** E has column rank five and `D=E((1/2)11^T-I)E^T` has rank five because the middle matrix is invertible. A PSD factorization through S^3 has two factor-span dimensions a,b at least five. Sylvester's inequality gives `a+b<=11`, so at least one span has dimension five; symmetry permits using it as the row span. Equality of column spaces then forces `A_ij=X_i+X_j` with independent X_i. Solving the trace equations using injectivity of E gives trace zero for indices in the column pair and one for the other indices, as asserted.

No A or B factor is zero, since D has no zero row or column. The zero diagonal entries force orthogonal ranges and hence singular A factors. The sum of the A factors is positive definite: otherwise their span would lie in S^2 and have dimension at most three, contradicting dimension five. Therefore `p(1)>0`, in particular p is not the zero polynomial.

At a rank-two A factor, its adjugate and its paired B factor are positive nonzero multiples on the same kernel line. Thus the three outside gradient entries are equal and strictly positive. At rank one the adjugate is zero. These observations establish both the gradient condition and the precise equivalence between an outside derivative of zero and rank one; rank zero was already excluded. They are essential to using the stronger Hessian condition.

The determinant identity now forces each pair sum into `{0,lambda/4,lambda/2}`. If lambda=0, all coefficients vanish, which contradicts the nonzero determinant polynomial. Division by the positive number |lambda| preserves every sign condition. For lambda=1 the admissible pair sums are `{0,1/4}`; for lambda=-1 they are `{-1/2,-1/4}`. Three distinct coefficient values would yield three distinct pair sums with a fourth coordinate. Two values each occurring twice would likewise yield three sums. Hence there are only the constant cases and the single-exceptional-coordinate cases. Enumeration gives exactly the manuscript's eight rows, up to permutation; it is exhaustive, not an experimental search.

**Eight obstructions.** In rows 1 and 5, the designated point is a zero of p but the full Hessian determinant is nonzero. In row 6, `p(1)<0`. Every other row has pair sum lambda/4 and a nonzero principal 4-by-4 Hessian minor, contrary to the forced rank-one pencil value. These exclude all eight possibilities and finish the lower bound.

### Lemma 4, `lem:two-layer`, and Corollary 5, `cor:six`

For rectangular Z_i of equal squared norm q, the graph-factor trace identities work for all positive integers a,b. The minus-layer scalar factors cancel within that layer. Both cross-layer products equal `q(t+t^(-1))+2<Z_i,Z_j>`, which is `c-D_ij` under the chosen equation. A positive solution exists when `c>=4q`; equality gives t=1 and creates no singular formula. All asserted factors remain PSD outer products.

For n=6, the two triple layers produce diagonal block D and off-diagonal block `3J-D`; directly computing intersections verifies both blocks. The n=5 coordinates have q=3/5, and `t=(3+sqrt(5))/2` satisfies `t+t^(-1)=3`, giving c=3. The leading submatrix D gives the lower bound four, and the two-layer construction gives the matching upper bound four.

### General bound `eq:general-upper` and monotonicity

For n=2r+1, centered incidence vectors of r-subsets need 2r coordinates and have squared norm `r(r+1)/(2(2r+1))` after the prescribed scaling. Padding and reshaping into an a-by-b rectangle with ab>=2r gives factor size a+b. For n=2r+2, the even-family blocks have c=r+1. The condition `c>=4q_r` holds, and `c/q_r-2=2+2/r`, giving the same factor size without an extra coordinate. This proves the claimed bound for every n>=3, including all canonical n>=5.

For integer d, fixing the sum a+b=s maximizes ab at floor(s^2/4); therefore the minimum allowable s equals ceil(2sqrt(d)). The elementary lower bound from arithmetic-geometric mean and the balanced integer choice agree, so no rounding gap exists.

The embedding from n-1 to n preserves the required two subset cardinalities: add the new element to row sets when n is even, to column sets when n is odd, and never to both. The intersections do not change. PSD rank is therefore nondecreasing and is at least four for n>=5.

## Independent exact checks

A separate Python standard-library calculation used `fractions.Fraction`, the directly differentiated formula

```text
Hess p = lambda Hess(e3) + (a.x) Hess(q)
         + grad(q) a^T + a grad(q)^T,
```

and rational Gaussian elimination for determinants. It reproduced the eight certificate values, in order:

```text
256/3, 1/4, 1, 9/4, 320, -5/8, -2, 1/4.
```

It separately verified the zero-value prerequisites of rows 1 and 5 and the pair-sum prerequisites of the rank-one rows. Ten further rational evaluations, one for each pair and with all a_i distinct, agreed with the general Hessian determinant identity. These finite checks supplement the structural proof and exhaustive eight-case reduction; they do not prove either universal statement by sampling.

## Primary-source comparison and remaining scope

The 2018 algorithm paper identifies the same family, retains bounds 3<=rank_psd(P5)<=4, and uses benchmark upper bounds six for P6 and P7. The manuscript's stated comparison with that table is accurate; the table is not an exact-rank claim. [Vandaele, Glineur, and Gillis, Section 4.2 and Table 2](https://arxiv.org/html/1707.07953)

No substantive gap was found. The exact family formula for n>=7 remains unresolved by this submission; specifically the new upper bounds at n=7,8 are five, with no matching lower bound five. The audited result should change the family entry only to partial resolution. Real PSD factors are essential; this report does not assess complex Hermitian rank, priority, exhaustive novelty, or numerical factorization algorithms.
