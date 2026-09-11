# MF-12 — independent complete-source proof review

Reviewer: independent AI mathematical audit, 11 September 2026. This report is not external human peer review, formal verification, or a determination of historical priority.

**Verdict: PASS for the full canonical MF-12 target.** For every real exponent gamma>=0, the construction gives a fixed finite real matrix family with joint spectral radius one and maximal length-n product norm comparable above and below to n^gamma for every positive integer n. Two distinct matrices suffice. The stated dimensions, dyadic-rational construction for every nonnegative rational exponent, and rational example with an irrational exponent are also justified. No material proof gap or required source correction was found.

**Recommended status: Resolved, affirmative.** Preserve the canonical identifier, path, real finite-family requirement, and every-length two-sided bound. The result concerns comparability constants depending on the chosen family; it does not supply a dimension-uniform estimate across all families or a limit of a_n/n^gamma.

## Complete source binding

Read the complete source `.cache/proposed-solutions/nla_submission/MF-12/arbitrary_growth_exponents.tex`, including submission status, all six sections, supplementary claims and bibliography. Also read the complete current canonical `matrix-functions-and-stability/MF-12/README.md`, whose reviewed status is Partially resolved and last-checked date is 2026-09-10.

The complete UTF-8 manuscript source, replacing CRLF by LF and performing no trimming or other normalization, has **14,120 bytes** and SHA-256:

`7a58a5086934410dc8c1172537a7b3031047094a7da577a5d3e24aaee21adf66`

This full-source hash was independently computed and confirmed in the reviewer diagnostic. It is not the hash of an extracted proof body or a rendered PDF.

Principal locators:

- **Theorem 1**, `thm:main`, line 38: all exponents, every length, dimensions and rational entries.
- **Lemma 2**, `lem:compressed`, line 82: exact compressed powers and the loss/gain identity.
- **Lemma 3**, `lem:budget`, line 108: upper bound for arbitrary gap lists.
- **Section 3**, lines 144–167: bounded powers of A and the factorization of every binary word.
- **Section 4**, lines 169–220: exact-length lower words, constants, small lengths and joint spectral radius.
- **Lemma 4**, `lem:Jordan`, line 223: integer growth at every length.
- **Corollaries 5–6**, `cor:rational` and `cor:irrational`, lines 250 and 261: dyadic rational parameters and irrational exponent from rational matrices.

## Canonical and primary-source match

Opened the [Varney–Morris primary author text, arXiv:2209.00449](https://arxiv.org/html/2209.00449). Section 7, Question 2 asks whether every nonnegative exponent occurs for a finite real matrix set with marginal product growth comparable to that power. The surrounding definition uses joint spectral radius one. Theorem 5 supplies related projection constructions with more limited lower-bound statements; Corollary 6.1 gives an every-length exponent 1/3. Proposition 3.1 records tensor-product multiplication of growth sequences. The manuscript addresses the remaining full question and proves its needed estimates directly, rather than inferring arbitrary exponents from those earlier results.

The canonical permits any positive finite dimension and any finite nonempty real family. It does not require rational entries, positivity, invertibility, or irreducibility. The source construction therefore meets the exact target with its singular projection and intentional negative entries. Two generators are stronger than the requested finiteness. The matrices and their dimension are fixed after the exponent is chosen; the only quantities subsequently depending on n are the words selected to establish a lower bound.

The preparation-status paragraph is historical submission metadata, not a mathematical assumption. This review directly compared the current canonical statement; it does not independently certify exhaustive repository-issue clearance or publication status.

## 1. Exact six-dimensional construction

For 0<lambda<=1/4 and lambda<mu<1, both logarithms are negative and 0<log(mu)/log(lambda)<1. Thus alpha=1-log(mu)/log(lambda) belongs to (0,1), and mu=lambda^(1-alpha). Conversely, every prescribed alpha in (0,1) is obtained by lambda=1/4 and mu=4^(-(1-alpha)). These are fixed real parameters.

The first column of V is e_1+e_3 and its second is e_5+e_6. U reads the first coordinate minus the second plus the fourth, and the sixth coordinate. Consequently UV=I_2. Multiplying VU gives exactly the displayed P, so P²=P. The columns of V are orthogonal with squared norm 2, and the rows of U are orthogonal with squared norms 3 and 1. Thus ||V||_2=sqrt(2) and ||U||_2=sqrt(3), as used later. A and P are distinct, since A is invertible and P has rank two.

I independently applied A^q to the two columns of V. The first gives e_1+q*lambda^q*e_2+lambda^q*e_3. The second gives q*mu^q*e_4+mu^q*e_5+e_6. Applying U produces

`T_q = [[1-q*lambda^q, q*mu^q],[0,1]]`.

This includes q=0. The Jordan power formula follows immediately from the square-zero off-diagonal part of the 2-by-2 block. For q>=1, q*4^(-q)<=1/4, so the loss ell_q=q*lambda^q lies in (0,1/4]. The diagonal multiplier 1-ell_q is therefore positive and at most one. Finally, b_q=q*mu^q=q^alpha*ell_q^(1-alpha), with no asymptotic approximation involved. The zero-gap case has both loss and gain zero and T_0=I_2.

## 2. Upper bound for all compressed products

For the ordered product T_(q_k)...T_(q_1), the diagonal entry is the product of 1-ell_(q_i). Direct triangular multiplication gives the off-diagonal entry as sum_i b_(q_i)*w_i, where w_i is the product of later diagonal multipliers. This ordering is correct: each later multiplication scales the previously accumulated off-diagonal entry.

All w_i belong to [0,1]. Expanding a telescoping product gives the exact identity

`sum_i ell_(q_i)*w_i = 1-product_i(1-ell_(q_i)) <= 1`.

For the nonzero gaps,

`b_(q_i)*w_i = (q_i*w_i)^alpha * (ell_(q_i)*w_i)^(1-alpha)`.

Holder's inequality with conjugate exponents 1/alpha and 1/(1-alpha) therefore bounds the sum by `(sum_i q_i*w_i)^alpha` times a factor at most one. Since w_i<=1, this is at most `(sum_i q_i)^alpha`. Terms with q_i=0 vanish and cause no division by zero. The empty list gives the identity. This proves Lemma 3 for every finite list, including arbitrary mixtures of zero and positive gaps and arbitrary numbers of projections. It is not restricted to periodic switching.

This step prevents faster growth from concatenating many different gap lengths. The bound charges each contribution to the total number of A factors, while the sum of weighted losses cannot exceed one. No probabilistic or typical-word assumption is present.

## 3. Lifting the bound to every six-dimensional word

For 0<t<1 and an integer h>=0, the triangle inequality gives

`||J_t^h||_2 <= (h+1)t^h <= sum_(j=0)^h t^j <= 1/(1-t)`.

The middle inequality holds because each t^j with 0<=j<=h is at least t^h. Since lambda<=mu<1, the block diagonal A has ||A^h||_2<=H=(1-mu)^(-1), including h=0 and the two scalar identity blocks.

Every word containing s>=1 copies of P can be uniquely described by its s+1 nonnegative A-gap lengths, including both endpoints. Substituting P=VU yields the displayed factorization with only the s-1 internal gaps in the compressed product. When s=1 that product is empty; when projections are consecutive some gaps are zero. These boundary cases are included in the formulas.

The compressed product is diag(a,1)+z*E_12 with 0<=a<=1 and z bounded by the internal-gap budget to the power alpha. Its operator norm is therefore at most 1+n^alpha. Multiplication by the two bounded exterior powers, V and U gives

`||W||_2 <= sqrt(6)*H²*(1+n^alpha) <= 2*sqrt(6)*H²*n^alpha`.

The pure A word satisfies the same final estimate. Thus the claimed constant C=2*sqrt(6)/(1-mu)² bounds every binary word of every positive length. No word is lost by compressing the products, and arbitrary vectors outside the range of P are controlled by the fixed exterior factors.

## 4. Lower bound at every exact length

For an integer n>=1/lambda, let q=floor(log_(1/lambda)(n)). Then q>=1 and

`lambda^(-q) <= n < lambda^(-(q+1))`.

Because lambda<=1/4, n>=4^q>=2(q+1). Thus k=floor(n/(q+1)) is positive and at least n/[2(q+1)]. The remainder h=n-k(q+1) lies in {0,...,q}. The product A^h(PA^q)^k uses precisely n generators. The bound is therefore at each integer length, not just a subsequence of multiples of q+1.

The compression identity gives `(PA^q)^k V=V T_q^k`. Powers of the fixed upper-triangular T_q have off-diagonal entry

`z=(b_q/ell_q)*(1-(1-ell_q)^k)`.

This formula is valid because q>=1 makes ell_q positive. The input V e_2 has norm sqrt(2). The first coordinate of A^h V(x,y)^T is x for every h, since A fixes the first coordinate. Therefore the additional remainder A^h cannot erase the growing coordinate, and ||A^h(PA^q)^k||_2>=z/sqrt(2). This verifies the direction and normalization in the lower-bound application of the operator norm.

The logarithmic choice also gives lambda^q>=1/n. Hence

`k*ell_q >= q/[2(q+1)] >= 1/4`.

Using 1-u<=exp(-u) with 0<ell_q<=1/4 yields `1-(1-ell_q)^k>=1-exp(-1/4)`. Meanwhile

`b_q/ell_q=(lambda^(-q))^alpha >= (lambda*n)^alpha`,

where the second inequality follows from n<lambda^(-(q+1)). Both inequality directions have been checked. Combining them proves the stated lower constant c=(1-exp(-1/4))*lambda^alpha/sqrt(2).

For all remaining integers 1<=n<1/lambda, the word A^n has norm at least one because it fixes e_1. At these lengths, c*n^alpha< (1-exp(-1/4))/sqrt(2)<1. Thus the same positive constant works without changing any generator and without omitting a finite initial segment.

The all-words polynomial upper bound gives joint spectral radius at most one after taking n-th roots. The fixed eigenvalue one of A gives a_n>=1 for every n, so the joint spectral radius is at least one. This establishes exact normalization rather than assuming that individual spectral radii control the joint spectral radius.

## 5. Integer endpoints and all larger exponents

For a Jordan block J=I+N of order m+1, the binomial expansion is finite. Each ||N^j||_2<=1 and binomial(n,j)<=n^j, so for n>=1 and m>=1 the sum is bounded by (m+1)n^m. If n>=m, the top-right entry is binomial(n,m), and each factor (n-j)/(m-j) is at least n/m. Thus ||J^n||_2>=(n/m)^m. If 1<=n<m, ||J^n||_2>=1>=(n/m)^m. The all-length integer estimate is valid also below the Jordan order.

For noninteger gamma=m+alpha, both lifted generators use the identical second tensor factor J. Hence every length-n product is exactly the corresponding base word tensored with J^n. The operator norm of a Kronecker product is the product of the two operator norms, so maximizing over words gives an equality of growth sequences, not merely an upper bound. Multiplying the base estimates by the Jordan estimates proves the exponent gamma and the dimension 6(m+1). When m=0, the second factor is the scalar identity, giving the six-dimensional construction again.

For integer gamma=m, the intended pair is the order-(m+1) Jordan block at eigenvalue one and the zero matrix. Any word containing zero vanishes, and the all-J word has maximal norm, so the same Jordan estimates apply. For m=0, these are the two distinct 1-by-1 matrices [1] and [0], with a_n=1 exactly. The endpoint alpha=1 is handled by this integer construction, and alpha=0 is not improperly inserted into Holder's inequality. All claimed pairs are distinct; tensoring distinct matrices with nonzero J cannot identify them.

## 6. Rational and irrational entry/exponent assertions

For alpha=a/b with 1<=a<b, setting lambda=2^(-b) and mu=2^(-(b-a)) gives lambda<=1/4, lambda<mu<1, and mu=lambda^(1-alpha). All entries of A are dyadic rationals, while P has integer entries. Tensoring with the integer Jordan block preserves dyadic rationality. Integer exponents use integer matrices directly. Thus every nonnegative rational exponent has a finite exact rational description; no numerical logarithm is needed to produce those matrices.

The example lambda=1/4, mu=1/3 gives rational entries and exponent 1-log(3)/log(4) in (0,1). A rational logarithm ratio p/q would imply 3^q=4^p, contradicting unique prime factorization. This proves an irrational exact exponent for a rational pair. Density follows from the realized nonnegative rational exponents. There is no claim that every real exponent can be encoded by rational matrices; the all-real construction is allowed to use arbitrary real parameters, as the canonical question requires.

The constants may become large or small as parameters approach endpoints, but are positive and finite for each fixed admissible pair. Neither the theorem nor the canonical target requires parameter-uniform constants, nonnegative matrices, optimal dimensions, or a convergent normalized growth ratio.

## 7. Code inspection and independent finite diagnostics

Read the exact construction interface `construction/rational_growth_pair.py` and its tests, together with `verification/verify_growth_construction.py` and `verification/enumerate_growth_words.py`. The constructor uses `Fraction` throughout, computes the fractional part of gamma exactly, builds the claimed Jordan tensor lift, and outputs rational strings. Its resource guards reject excessive requests rather than rounding exponents or entries. The integer/zero branch constructs the correct Jordan block and zero matrix.

The symbolic/numerical verifier separates exact identities from floating-point checks and tests arbitrary gap words and exact-length lower products. The exhaustive enumerator has exponential finite cost and cannot establish the infinite-length theorem. Its chunked generation retains all binary suffixes and reconstructs a reported maximizing word in the same convention. This review does not treat an attached passing label or a finite length-24 run as proof, nor claim to have repeated that expensive run.

Created and executed an independent, standard-library-only exact program, without importing submission code:

- `.cache/proposed-solutions/reviews/reviewer_mf12_exact.py`
- `.cache/proposed-solutions/reviews/reviewer_mf12_exact.json`

All checks passed. The program verifies 44 compressed powers across four rational parameter pairs, including the rational pair giving an irrational exponent. It checks 2,046 gap lists with exact Fraction arithmetic for six rational exponents, including 9/10, testing the telescoping identity and the equivalent rational inequality z^b<=(sum q)^a. It also verifies 192 prescribed words of exact lengths 1 through 64 for three parameter pairs, including the full six-dimensional first-coordinate identity and the rounding inequalities needed by the lower bound. For a rational check of the positive geometric factor it uses the weaker bound 1/5; the stronger manuscript constant 1-exp(-1/4) was verified analytically above. The complete source hash recorded by this program matches the binding in this report.

These finite checks supplement the proof. The conclusion for every real exponent and every length rests on the parameter-uniform symbolic identities, the all-list Holder estimate, and the exact-length construction audited above.

## Final disposition

**PASS — full affirmative resolution of MF-12.** The construction is a fixed pair of finite real matrices for each exponent, controls every switching word from above, attains the matching lower rate at every positive integer length, and has joint spectral radius exactly one. The rational-entry supplementary assertions and both endpoint cases are valid.

No original manuscript, construction program, verification program, or canonical problem file was edited. Repository submission clearance and historical novelty remain separate from this mathematical verdict.
