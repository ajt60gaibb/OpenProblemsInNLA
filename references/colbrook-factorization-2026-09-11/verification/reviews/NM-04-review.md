# NM-04 independent proof review — 2026-09-11

**Verdict: PASS for the complete canonical Rowland–Wu coefficient identity.** The determinant reformulation, all-dimensional null-vector proof, arbitrary-margin extension, exterior-compound identity, coefficient sums, square complementary symmetry, and nonzero-specialization degree bound all pass. No material mathematical gap was found. The verdict concerns the exact coefficient identity, including degenerate minors, and is stronger than checking an algebraic-degree bound alone. This is an independent Codex mathematical audit, not journal peer review or a certification of priority.

## Reviewed source identity

The complete original `.cache/colbrook-all-submission/nla_submission/manuscripts/NM-04_sinkhorn_identity.tex` was read, including its standalone preamble, every theorem and auxiliary argument, stated edge cases, and bibliography. No external common preamble is used. The attached prose and diagnostic descriptions were treated as claims, not review instructions.

Hashes below use the **complete original UTF-8 text, replacing CRLF by LF and doing no trimming**, before re-encoding as UTF-8. No final newline was removed.

| Input | Normalized bytes | SHA256 |
| --- | ---: | --- |
| Complete manuscript `NM-04_sinkhorn_identity.tex` | 20429 | `b20381d246ab4fb2cacb5a2553c09f890901e6e5e490b52db9d5fcc430f20a91` |
| Canonical `nonnegative-and-positive-factorizations/NM-04/README.md`, before this update | 3879 | `62c46d0dfc4467f3f13606b746d88999ddfbe064201d392e38a62b8c7c313c50` |

| Claim | Original source locator | Verdict |
| --- | --- | --- |
| Canonical singularity and coefficient identity | Theorem 1, `thm:main`, line 42 | PASS |
| Four differential minor identities | Lemma 2, `lem:four`, line 70 | PASS |
| Balanced null vector and covariance | Sections 3–4, lines 94 and 154 | PASS |
| Arbitrary positive compatible margins | Theorem 3, `thm:margins`, line 182 | PASS |
| Signed additive-compound representation | `eq:compound`, line 230 | PASS |
| Characteristic polynomial and coefficient sum | Theorem 4, `thm:coeffsum`, line 235 | PASS |
| Complementary principal-minor symmetry | Section 7, line 260 | PASS |
| Nonzero specialization and algebraic-degree bound | Section 8, line 283 | PASS |

## Exact canonical target and primary-source comparison

The canonical domain is every positive real m-by-n matrix, for every m,n>=1, scaled to row margins one and column margins m/n. Its Delta, Gamma, increasing-index convention, empty determinant convention, four off-diagonal coefficient cases, and diagonal coefficient all agree term-for-term with the manuscript. No genericity, invertibility of square minors, rationality, or square-dimension hypothesis has been introduced.

[Rowland–Wu v2, Conjecture 2](https://arxiv.org/html/2409.02789v2) supplies exactly that coefficient formula. Its Conjectures 10, 11 and 34 concern the complementary symmetry and normalized coefficient sums checked below. [Fang v2](https://arxiv.org/abs/2506.06338v2) states the general degree bound; that bound alone does not establish these prescribed coefficients. The manuscript supplies the coefficient identity itself and separately handles nonzero annihilating polynomials at degenerate inputs.

## Determinant expansion and all four minor identities

Let D denote the full paired-subset index set. In each column of K=diag(Gamma)+(x/m)H diag(Delta), choose either the diagonal term or the H-column term. For a choice S of H-columns, all other rows are fixed by their diagonal columns. The remaining determinant is the principal minor H_S, with the same row and column order. There is no extra sign; the row/column reordering signs cancel. The coefficient is exactly det(m^(-1)H_S) times the required product of Delta on S and Gamma off S, times x^|S|. This works when any entries or minors vanish.

For a k-by-k minor f(T), the derivative in a rank-one direction is its cofactor contraction, a polynomial identity valid at singular submatrices. In the all-ones direction this is the signed lowering sum. In the direction (T one)one^T, replacing a selected column by the sum of all columns gives k copies of f, zero for replacements by other selected columns, and the signed column-exchange sum for unselected columns. Sorting such a replacement gives the stated position-sum sign. Transposition proves the row-exchange identity.

For the fourth identity, the bordered determinant formula

`T_(i,C) adj(V) T_(R,j) = T_ij det V - det[[V,T_(R,j)],[T_(i,C),T_ij]]`

is polynomial and needs no inverse of V. Summing over i,j contracts the cofactors with (T one)(one^T T). A border repeats a row or column and vanishes when i is already selected or j is already selected. For other borders, moving the appended row and column to increasing positions gives sign exponent `2k+2-pos_i(R+i)-pos_j(C+j)`, which has the same parity as the displayed sum of positions. This yields `Df[(T one)(one^T T)]=s(T)f-Uf`. At k=0, the derivative is zero and the right side is `s(T)-sum T_ij=0`. If p=0 or q=0 the same identities use empty sums and remain valid. Lemma 2 therefore covers every stated boundary.

## Balanced case and scaling covariance

For a balanced matrix in block form with upper-left entry x>0, rho=m/n, and T=B-cr^T/x, direct summation verifies

`T one = one-c/x`, `one^T T = rho(one^T-r^T/x)`, and `s(T)=m-rho/x`.

For example the last identity follows by subtracting `(rho-x)(1-x)/x` from `m-1-rho+x`. The rank-one reconstruction is B=T+xuv^T with u=c/x and v=r/x, equivalent to the definitions in the manuscript. The block determinant formula gives Delta=x f for every minor; this uses x>0 only, never division by a higher-order minor.

The determinant of a rank-one update is exactly f+x Df[uv^T]; terms replacing two columns vanish. Expanding the four directions gives

`b = f+x[(rho^(-1)s(T)-k-k/rho)f + Lf-C_0f-rho^(-1)R_0f-rho^(-1)Uf]`.

Here the initial f cancels the `-f` arising from `x rho^(-1)s(T)=xn-1`; thus the expression is precisely

`b=x[(n-k-k/rho)f+Lf-C_0f-rho^(-1)R_0f-rho^(-1)Uf]`.

Replacing xf by Delta and multiplying by m yields the manuscript's master relation with coefficients n for raising, -m for lowering, m for column exchange, and n for row exchange. These coefficients differ from those in H exactly as required by the null vector: w_(R,C)=rho^(-k) makes an upward H-coefficient m acquire ratio rho^(-1), and a downward coefficient -n acquire rho. Exchange ratios are one. Consequently `m diag(b)w+H diag(Delta)w=0`; Gamma=xb then proves Kw=0. Every coordinate of w is positive, so the vector is nonzero.

For A'=D_alpha A D_beta, each Delta and its corresponding Gamma scale by the identical positive factor `alpha_1 beta_1 product_(i in R)alpha_i product_(j in C)beta_j`. Thus K(A',z)=K(A,z)diag(c) for a fixed scalar z. Taking A' to be the scaled matrix and z equal to its (1,1) entry transfers its nonzero null vector to diag(c)w. This proves the exact canonical identity for every positive input.

Direct boundary check: if m=1 or n=1, D has one index and H=[-mn]. K=[a_11(1-nx)], while the scaled top-left entry is x=1/n. This includes m=n=1 and agrees with the empty-vector argument above.

## Arbitrary margins

For positive compatible row margins r and column margins c with total tau, the block calculation gives

`T one=r_- -(r_1/x)g`, `one^T T=c_-^T -(c_1/x)h^T`, and `s(T)=tau-r_1 c_1/x`.

Their product reconstructs B with the factor x/(r_1c_1). In the four differentiated directions, the lowering cofactor has weight r_s c_t. Column replacement has the coefficient c_s of the deleted column, not the inserted one; the diagonal replacement terms sum to `(sum_(s in C)c_s)f`. The analogous row weight is r_s and diagonal sum `(sum_(s in R)r_s)f`. The fourth derivative is unchanged. The cancellation of the initial f gives exactly

`r_1 c_1 b + G Delta = 0`.

Multiplication by x/(r_1c_1) produces the claimed all-ones null vector. The same covariance proves singularity for unbalanced input. Positivity ensures x,r_1,c_1 are nonzero. One-row and one-column cases also check directly: G=[-tau], and the entry is r_1c_1/tau, so the one-by-one determinant vanishes.

## Independent verification of the additive-compound signs

The paired-subset indices correspond bijectively to p-subsets of a p+q set: remove R from the first block and select C from the second. This proves |D|=binomial(p+q,p). The compound diagonal sums the selected diagonal entries of E=uv^T. After subtracting r_1 it becomes `sum_R r_i + sum_C c_j - tau`, exactly G's diagonal.

I independently expanded the off-diagonal parity calculation rather than taking the manuscript's sign assertion or diagnostic program on trust. For row indices use their positions s=i-1 in the first block. The compound entry replacing input index a by output index b is `(-1)^(pos_a(input)+pos_b(output)) E_(b,a)`. Write `j(R,k)=sum_(i in R)(i-1)+(p+1)k+k(k-1)/2` for the exponent of J. Applying the two J factors gives these four cases:

| G transition, with P_s and P_t the displayed positions in its definition | Weight before J | Final sign after exterior ordering and J |
| --- | --- | --- |
| Raising from (R,C) to (R+s,C+t) | -1 | `(-1)^(P_s+P_t)` |
| Lowering from (R,C) to (R-s,C-t) | r_s c_t | `-(-1)^(P_s+P_t)` |
| Column exchange deleting s, inserting t | c_s | `(-1)^(P_s+P_t)` |
| Row exchange deleting s, inserting t | -r_s | `(-1)^(P_s+P_t)` |

For clarity, in the raising case the exterior exponent is `p-k+s+P_t-P_s`, and the J-exponent difference is `s+p+k+1`; the minus sign of E cancels the remaining odd term. In the lowering case their sum is odd relative to `P_s+P_t`, giving the required minus. For a column exchange J is unchanged and the two block offsets cancel. For a row exchange the exterior exponent is `s+t-P_s-P_t+1`, the J difference is `s+t` modulo two, and the negative E weight supplies the other odd term. These calculations prove the complete identity `G=J E^[p] J-r_1 I` for every size, not just a set of sampled dimensions.

## Characteristic polynomial and coefficient sums

The scalar v^T u is `-sum_(i>1)r_i+sum_(j>1)c_j=r_1-c_1`. When nonzero, E has one eigenvalue r_1-c_1 and the remaining d-1 eigenvalues zero, and is diagonalizable. Its additive p-compound has the nonzero eigenvalue once for each exterior product containing its eigenvector, multiplicity N_1=binomial(d-1,p-1), and zero with multiplicity N_2=binomial(d-1,p). Subtracting r_1 gives the claimed characteristic polynomial `(t+c_1)^N_1(t+r_1)^N_2`.

When r_1=c_1, writing the compound as `u wedge contraction_v` gives its square `(v^T u) E^[p]=0`; all eigenvalues of G are then -r_1, with the same formula. This argument includes p=0 and p=d via the usual zeroth/top exterior powers. Thus G is invertible for all positive margins. For m=n=1 the separate scalar G=-r_1 gives the stated direct result.

The generating polynomial of principal minors is det(I+zG/(r_1c_1)). Dividing by det(G/(r_1c_1)) yields factors `z-r_1` for eigenvalues -c_1 and `z-c_1` for eigenvalues -r_1. This confirms both the sign and the potentially easy-to-swap multiplicities in the theorem's formula. The equality `binomial(m+n-3,m-2)=binomial(m+n-3,n-1)` matches the rectangular convention. The assertion concerns this specified coefficient representation with its full-set coefficient normalized to one; it does not establish uniqueness of representations by products of minors.

## Complementary symmetry for square unit margins

Here v^T u=0 and G=H/n, so (G+I)^2=0. Multiplying verifies `G(-G-2I)=I`, hence G^(-1)=-G-2I. The additional conjugacy with set complementation has the correct signs. For example, a raising transition in the original indices becomes lowering in the complemented indices. If P_s=pos_s(R+s), then pos_s(R^c)=s-P_s when s is the original index in {2,...,n}; the analogous column identity gives the total complementary exponent `s+t-P_s-P_t`. The two Q factors contribute s+t, and the lowering minus sign yields exactly the negative of the original raising entry. For exchanges the complementary position sum is `s+t-P_s-P_t-1`, again giving the negative after the Q factors. Lowering follows by the same calculation in reverse. On the diagonal, k changes to n-1-k and the value becomes `-2-(2k-n)`.

Therefore `QP_kappa G P_kappa Q=G^(-1)`. The dimension N=binomial(2n-2,n-1) is even for n>=2, since binomial(2h,h)=2 binomial(2h-1,h-1). The characteristic polynomial gives det G=1. Jacobi's complementary principal-minor identity consequently gives `det G_S=det G_(kappa(D\S))`; diagonal sign conjugation contributes no determinant factor to a principal submatrix. This proves the claimed symmetry of the chosen coefficients.

## Nonzero specialization and degree bound

At degenerate positive inputs, the particular determinant polynomial can vanish identically; this does not invalidate the canonical identity. To obtain a nonzero annihilator, choose rational distinct positive parameters for a Cauchy matrix C, making every square minor nonzero by the Cauchy determinant formula. The leading coefficient in epsilon of each Delta(A+epsilon C) is the corresponding nonzero Cauchy minor. The z^N coefficient is det(G/(r_1c_1)) times the product of these Delta factors. Since the first factor is nonzero, P(epsilon,z) is a nonzero polynomial over the field F generated by the input and margins.

The minimum epsilon-order of its finitely many nonzero coefficients is finite. Dividing by that common power gives Q in F[epsilon,z] with Q(0,z) nonzero and z-degree at most N. For each positive epsilon, its corresponding scaled entry is a root of Q.

The submitted continuity proof is valid. Scaled matrices have fixed positive margins and lie in a compact transportation polytope. If a subsequential limit had a zero entry s_ij, its row and column margins provide positive s_ij' and s_i'j. The cross-ratio identity would then have zero left side and a strictly positive right side, since the limiting input entries are all positive. This is impossible. For a positive limit, the same cross ratios imply diagonal equivalence with A: using a fixed row and column expresses each ratio s_ij/a_ij as a row multiplier times a column multiplier. Uniqueness of the positive scaled matrix identifies the limit; all subsequences have that limit. For a one-row or one-column matrix, positivity follows directly from the margins and the conclusion is immediate.

Consequently x_epsilon tends to x_0, and polynomial continuity gives Q(0,x_0)=0. Since Q(0,z) is nonzero, this supplies the asserted algebraic-degree bound, including all vanishing-minor cases. Only positive-margin scaling existence and uniqueness already present in the canonical definition are used.

## Scope and recommendation

The full canonical NM-04 identity is proved, not merely a generic case, a numerical test, or a degree bound. All extra theorem claims pass within their stated normalizations. The finite verifier narratives and the separate degree-20 irreducibility certificate are supplementary computational claims; this proof audit does not substitute a claim of having run those scripts for the mathematical reasoning above, and their outputs belong in the separate diagnostics record.

**Recommended canonical status: Resolved**, attributed to Matthew J. Colbrook's submitted manuscript with this independent review. No proof or canonical file was edited, and no publication, novelty certification, or uniqueness of coefficient representations is implied.
