# FR-04 planar/projection manuscript: independent review — 2026-09-11

**Verdict: PASS for the complete auxiliary manuscript; FR-04 remains open.** The sharp weighted planar inequality, determinant-weighted residual-energy lemma, general submatrix bound, and polynomial corollary are valid. The bound is of order L n^(-3/2) at (2n-1)-by-n size and does not establish the exponential upper bound required by the canonical conjecture. No material mathematical gap was found in the claims actually made.

This is an independent Codex mathematical audit. The full proof and primary source comparisons were checked; no original proof or canonical file was edited. Mathematical correctness is separate from publication or historical priority.

## Source identity and locators

Reviewed source: `.cache/colbrook-frames-submission/frames_submission/manuscript/planar_projection_bound.tex`, including its standalone preamble and bibliography. SHA256 hashes the **entire original UTF-8 text after replacing CRLF by LF, without trimming or removing its final newline**.

| Input | Normalized bytes | SHA256 |
| --- | ---: | --- |
| Complete `planar_projection_bound.tex` | 8310 | `e6919a807c600c3774f722955e2aeeeb6cee649ad3abfb3428acc3003f9bce2e` |
| Canonical `frames-and-matrix-designs/FR-04/README.md` before the update | 3085 | `278465b37c1ad7b7e6eea3d4d1b53a7cb00e2b74d94540d1bc04efdd0bf1c9f5` |

| Claim | Original manuscript locator | Verdict |
| --- | --- | --- |
| Sharp total-energy planar bound | Theorem 1, `thm:plane`, line 23 | PASS |
| Determinant-weighted residual-energy choice | Lemma 2, `lem:energy`, line 72 | PASS |
| General square-row-submatrix bound | Theorem 3, `thm:general`, line 101 | PASS |
| Minimally redundant polynomial bound | Corollary 4, `cor:critical`, line 122 | PASS |
| Universal exponential bound | Canonical FR-04; discussed at line 136 | Not proved or disproved |

## Exact target and source comparison

The canonical conjecture asks for fixed absolute C>0 and beta in (0,1) such that every real full-spark (2n-1)-by-n matrix obeys omega(A)<=C L(A) beta^n. The manuscript controls the same minimum least singular value of n-row submatrices, with the same largest-row-norm normalization. Its general theorem applies even without full spark, which is a legitimate strengthening of the domain of its polynomial statement; it does not strengthen polynomial decay to exponential decay.

[Balan–Wang, printed pp. 483–484](https://www.cscamm.umd.edu/publications/ACHA2015paper_CS-16-05.pdf) already records a preliminary O(L n^(-3/2)) bound and then states the stronger exponential Conjecture 5.1. [Liu, Theorem 2.7](https://files.ele-math.com/articles/oam-18-17.pdf) gives the sharp maximum-row-norm planar bound and its equally spaced projective-line configuration. The manuscript instead uses total squared row norm in the planar step. This audit certifies the argument, not priority for that weighted formulation.

## Weighted planar inequality

Let t be the minimum pairwise least singular value. If t=0, the claimed bound is immediate, including E=0. Otherwise every row is nonzero and each pair is independent, so its unoriented row line is distinct. Each two-row Gram matrix has least eigenvalue at least t^2. Thus q_i=||b_i||^2/t^2>=1, and positivity of the determinant of that Gram matrix minus t^2 I gives

`|cos(theta_i)| <= sqrt(1-1/q_i) sqrt(1-1/q_(i+1))`.

The lines can be ordered around the real projective circle with consecutive gaps theta_i in (0,pi) summing to pi. Even if a gap exceeds pi/2, the displayed absolute-cosine inequality implies theta_i is at least the arccosine of its nonnegative right side. Hence no assumption that all consecutive gaps are acute is hidden in the proof.

For g(z)=arccos(exp z), direct differentiation gives

`g''(z)=-exp(z)/(1-exp(2z))^(3/2)<0`.

Writing the two factors inside the arccosine as the exponential of the mean of log(1-1/q_i) and log(1-1/q_(i+1)), concavity gives exactly the average of f(q_i) and f(q_(i+1)), where f(q)=arccos(1-1/q). At q=1, the logarithm tends to minus infinity but the arccosine limits exist; taking limits proves the same inequality. This handles rows whose norm equals t.

Independently, `f'(q)=-1/[q sqrt(2q-1)]` and

`f''(q)=(3q-1)/[q^2(2q-1)^(3/2)]>0`.

The function is convex and decreasing on q>=1, with a finite endpoint limit. Summing over cyclic gaps and applying Jensen yields

`pi >= sum_i f(q_i) >= M f(E/(M t^2))`.

Since arccos is decreasing, this implies `M t^2/E <=1-cos(pi/M)=2 sin^2(pi/(2M))`. Taking nonnegative square roots proves the theorem with the stated constant. The argument also covers M=2, where the two cyclic gaps are complementary and the sharp configuration is an orthogonal pair.

For sharpness, equal row lengths r=sqrt(E/M) on equally spaced unoriented lines have smallest projective separation pi/M. A pair's squared least singular value is r^2(1-|cos alpha|). The minimum is therefore r^2(1-cos(pi/M)), attaining the claimed bound. This proves sharpness for the fixed total-energy planar problem. It does not claim that the later high-dimensional bound has the optimal constant or decay order.

## Determinant weights and the residual-energy identity

Assume rank A=n and put k=n-2. For each k-row set S, w_S=det(A_S A_S^T) is nonnegative. Since A has full column rank, some k-set is independent (and for k=0 the empty-set determinant is one), so the total weight is positive.

For a positive-weight S and i not in S, the Schur complement of the Gram matrix of S gives

`det Gram(S union {i}) = det Gram(S) ||P_S a_i||^2`.

This is the squared residual after orthogonal projection away from the span of S. For zero-weight S, rank(S)<=k-1 and adjoining one row cannot give rank k+1. Both sides are therefore zero, so the equality can be summed over all sets without inverses of singular Gram matrices. Rows already in S have zero projected residual and contribute nothing.

Each (k+1)-set T occurs in the sum once for every removed index, namely k+1 times. The determinant-weighted mean of the total residual energy is consequently

`(k+1) e_(k+1)(lambda)/e_k(lambda)`.

Here lambda consists of the n positive eigenvalues of A^T A. Summing principal Gram minors is exactly the corresponding elementary symmetric polynomial: one may use Cauchy–Binet, or the characteristic polynomial of AA^T whose remaining m-n eigenvalues are zero. The use of row subsets and the factor k+1 are correct.

Set a_j=e_j(lambda)/binom(n,j), with a_0=1. Newton's inequalities make a_j log-concave, so a_(j+1)/a_j is nonincreasing and in particular a_(n-1)/a_(n-2)<=a_1=E/n. Since

`a_(n-1)/a_(n-2) = ((n-1)/2) e_(n-1)/e_(n-2)`,

the weighted mean `(n-1)e_(n-1)/e_(n-2)` is at most 2E/n. At least one positive-weight set has residual energy no larger than that mean. This verifies the normalization and the factor two. For n=2, S is empty and the assertion is the direct equality E=2E/n.

## Projection to a plane and the square submatrix

For the selected independent set S of n-2 rows, its orthogonal complement has dimension exactly two. There are M=m-n+2 remaining rows. Their projections have total squared norm at most 2E/n, since the rows in S project to zero. The planar theorem gives a pair i,j and a unit vector x in that plane whose total squared measurements are at most

`[4E/(nM)] sin^2(pi/(2M))`.

Every row of S annihilates x. Thus the same energy bound holds for the n-by-n submatrix on S union {i,j}, giving its least singular value at most the claimed square root. Taking the minimum over n-row sets proves Theorem 3. It does not incorrectly identify a projected pair's singular value with that of the entire submatrix; it uses the same explicit test vector to obtain the needed upper bound.

If rank A<n, every n-row submatrix is singular and omega_n(A)=0, so the bound is immediate. The m=n boundary gives M=2 and reduces to the familiar smallest-singular-value bound sqrt(E/n). Zero projected rows or collinear projected pairs simply give t=0 and an even stronger conclusion. All these degeneracies are covered.

## Critical row count and comparison with the exponential target

For m=2n-1, M=n+1 and E<= (2n-1)L^2. Substitution yields exactly

`omega_n(A) <= 2L sqrt((2n-1)/(n(n+1))) sin(pi/(2(n+1)))`.

As n tends to infinity the right side is asymptotic to pi sqrt(2) L n^(-3/2). The manuscript correctly identifies this as the asymptotic expression for an upper bound, not an asymptotic formula for omega_n(A) for every matrix.

For every fixed beta in (0,1), n^(-3/2)/beta^n tends to infinity. Therefore no choice of a dimension-independent constant can turn this displayed polynomial estimate into the requested exponential estimate. The projection controls one residual plane and its M directions; it supplies no cumulative control across all square bases that would imply exponential decay. Nor does the sharpness of the planar lemma produce a high-dimensional family with omega_n(A) bounded below polynomially, which would be needed for a disproof of the conjecture. Both possibilities in the canonical exponential question remain open.

The warning about using a small determinant alone is correct: it is a product of n singular values. A small product need not force the smallest singular value to be exponentially small without quantitative control of the other factors. No determinant claim in the proof substitutes for this missing step.

## Verification scope and recommendation

The derivative signs, Gram-volume identity, normalized Newton ratios, and asymptotic constant were independently checked above. Finite numerical tests or symbolic checks in the companion verification workflow are supplementary and cannot strengthen the conclusion to an exponential one.

**Recommended canonical status: retain Open for FR-04.** Add this manuscript only as an independently checked auxiliary polynomial estimate, with its historical scope stated accurately. The same polynomial order was already recorded by Balan–Wang, and the universal exponential target is neither proved nor disproved. No proof repair is needed, and no blanket solved status is justified.
