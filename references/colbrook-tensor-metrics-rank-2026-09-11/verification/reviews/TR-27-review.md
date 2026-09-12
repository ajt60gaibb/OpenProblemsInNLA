# TR-27 — independent mathematical review

Date: 11 September 2026.

**Verdict: PASS — full negative resolution of the canonical universal implication.** The manuscript constructs a smooth, irreducible, reduced, nondegenerate complex projective curve X in P^11 and a point p with border X-rank 2, X-rank 3, and rank 9 relative to the Segre image of X × X. Its stronger assertion of any prescribed finite delay of strict submultiplicativity also passes. No source correction is required.

## Reviewed source and binding

- Complete original manuscript: `.cache/tensor20/submission/TR-27/solution.tex`, including abstract, all proofs, explicit coordinates, eventual-power argument, verification/scope text and bibliography.
- Normalization: decode the complete UTF-8 source, replace CRLF by LF, re-encode UTF-8; no trimming or other changes.
- Normalized length: **14,343 bytes**.
- Complete normalized SHA256: **`db7d556699d5021a9da6674ef491561c8af631d8537d99e21f427a82c7d1dca4`**.
- Canonical target read with `git show origin/main:tensor-computations/TR-27/README.md`; `origin/main` resolved to `aaa88c40fbf58e8cebc335021b3c5cd108c357e4` during this review.
- Read the entire accompanying `TR-27/verify.py`. Mathematical conclusions below were checked independently of its assertions and output. The parent reviewer handles execution of the supplied verifier.

This review did not modify the manuscript or canonical page, and does not determine submission eligibility, priority or publication clearance.

## Exact target and primary-source comparison

The canonical question permits every irreducible reduced nondegenerate complex projective variety, and uses the Segre image of X × X in P(V tensor V). A smooth projected rational normal curve is an admissible variety; it need not be a full Veronese variety or a Segre variety. All coefficients in rank decompositions are unrestricted complex numbers. The manuscript uses exactly these definitions, and keeps all product factors separate.

The primary paper defines its class of varieties in Section 1 and states precisely this implication in Conjecture 1.1. Its immediately following discussion concerns a saving at some sufficiently large power. Its Lemma 2.5 independently corroborates the contraction step used in the manuscript's product lemma. [Ballico–Bernardi–Gesmundo–Oneto–Ventura, arXiv:1909.03811v2](https://arxiv.org/html/1909.03811v2).

The publisher's full text of the 2025 survey also states the general-variety implication as Conjecture 4.9. It does not restrict that conjecture to the binary-form or ternary-cubic subclasses mentioned before it. [Oneto–Ventura, Ranks of tensors: geometry and applications](https://link.springer.com/article/10.1007/s40574-025-00472-9).

The supplied construction therefore negates the actual universal target, rather than merely resolving a subclass. It makes no claim to disprove the versions restricted to Segre or Veronese varieties. In particular, a non-linearly-normal projection of a rational normal curve does not contradict the established binary-form result for the rational normal curve in its original embedding.

## 1. Tangent-vector rank — Lemma 2, lines 61–78

The vector convention c_D(t) = (1,t,...,t^D) is used consistently; no binomial coefficient normalization is silently introduced. Any at most D+1 distinct curve points are independent, including a point at infinity: with that point present, use the first s−1 rows for the finite points and the final coordinate for infinity.

For a proposed decomposition of e_1 using ell ≤ D−1 distinct points, the annihilator f(T) = T product(T−a), over finite nonzero parameters, has nonzero coefficient of T. It vanishes at every finite parameter, including zero when present. Without infinity its degree is at most ell+1 ≤ D; with infinity its degree is at most ell ≤ D−1, so its coefficient in degree D vanishes too. The associated linear functional annihilates every proposed summand but not e_1. This proves the lower bound uniformly for finite parameters, zero and infinity, without any genericity assumption.

For the upper bound, among j = 0,...,D the only exponent j−1 divisible by D is zero, since D ≥ 2. The D-th-root-of-unity sum therefore equals e_1 exactly. Thus the lemma proves rank exactly D.

## 2. Product lower bound — Lemma 3, lines 80–97

The hypothesis concerns all sets of at most K distinct projective points, not merely generic sets. Given a hypothetical decomposition of length L ≤ r^k−1 ≤ K, collect all distinct points occurring in each separate factor and choose fixed representatives. These representatives form a linearly independent set A_j in that factor. Any original representative differs only by a nonzero scalar, which can be absorbed in its summand coefficient.

Since v is nonzero, a functional with value 1 on v exists. Contracting all other factors gives v in span(A_j), even if some contracted summands vanish. Its unique expansion in A_j has at least r nonzero coordinates, by the definition of X-rank. The Cartesian product of the independent sets A_j is an independent tensor-product basis of their product span. Consequently v^tensor k has at least r^k nonzero coordinates in that basis. Each original summand occupies exactly one coordinate; repeated products or cancellations can reduce, but cannot increase, the number of coordinates supported by L summands. This is impossible when L < r^k.

This proves the universal lower bound against arbitrary complex decompositions, with unrelated parameter choices in different factors. It does not assume symmetry of a decomposition, positivity, a common parameter set, or use of only the displayed r points. The expansion of an r-term decomposition gives the matching upper bound. The k = 1 case is also valid (the contraction over no factors is the identity).

## 3. Projection and rank of p — Section 3, lines 99–138

For arbitrary r ≥ 3, m ≥ 2 set D = r^m+r and choose distinct nonzero a_i. The center vector z = e_1−sum_i c_D(a_i) is nonzero directly because its zeroth coordinate is −r. Subadditivity applied to e_1 = z+b and Lemma 2 gives rank_C_D(z) ≥ D−r = r^m. Thus the center is off C_D and the quotient restricts to a morphism on the entire curve. Its image is closed and irreducible by projectivity and is reduced by the stipulated reduced structure. Surjectivity of the quotient and spanning of C_D prove nondegeneracy in P^(D−1).

Proposition 4 (line 112) is correct. Lift any s ≤ K = r^m−1 distinct image points to distinct curve points. A relation among their images lifts to a relation with right side lambda z. If lambda is nonzero it contradicts the center-rank bound. If lambda is zero it contradicts Vandermonde independence, since s < D+1. This handles every possible set on X.

The projection cannot identify two distinct curve points: that would place z in their span and give rank at most 2. Accordingly the r displayed image points are distinct. They are independent because r ≤ K, and their sum is a nonzero representative v of p. If v had a shorter expression, its union with the displayed r-term expression would contain at most 2r−1 ≤ r^m−1 points. Independence of that union forces equality of the coordinates in both expressions, including every original coefficient 1. A shorter expression is impossible. This proves rank_X(p) = r and in particular p is not on X.

The difference quotient of the projected curve at t = 0 tends to the nonzero vector v. For sufficiently small nonzero t, the difference quotient is nonzero and has X-rank at most 2. Euclidean convergence implies membership in the Zariski closure of that rank locus. Border rank is therefore at most 2; it cannot be 1 because X is closed and p is not in X. This proves border rank exactly 2.

For every 1 ≤ k ≤ m, r^k−1 ≤ K, so Lemma 3 proves exact rank r^k. The theorem has the right quantifiers: each prescribed finite r,m determines a curve, rather than one fixed curve retaining multiplicativity for all powers.

## 4. Smoothness — Section 3.1, lines 140–159

The claimed center border rank r+2 is correct. The upper bound follows by taking the tangent-vector degeneration for e_1 and subtracting the fixed r curve vectors. This gives actual vectors of rank at most r+2 converging to z.

D = r^m+r ≥ 2r+2 for the stated parameters, so all entries in the (r+2)-square Hankel matrix use available coordinates. A finite curve vector maps to u(a)u(a)^T, of matrix rank 1. The infinity vector maps to zero if D > 2r+2, or to the bottom-right coordinate matrix if equality holds; in either case its rank is at most 1. Hence rank ≤ s on sums of s curve vectors and on their Zariski closures, since matrix minors are polynomial. This justifies the border-rank lower bound, including infinity.

The asserted factorization H = B M B^T is entrywise exact: u(0)u'(0)^T + u'(0)u(0)^T contributes delta_(i+j,1), and the remaining columns contribute minus sum a_nu^(i+j). A polynomial of degree at most r+1 annihilating all columns of B has a double root at zero and the r distinct nonzero roots a_i, so it must vanish. Thus B and M are invertible and H has rank r+2.

In particular z is outside the border-rank-two locus and hence off every secant and tangent line, including those involving infinity. Equality of two projected points would put z on their secant; vanishing of the projected differential would put it on the tangent. Neither can occur. The resulting injective immersion from the smooth compact complex curve is an embedding, and its closed algebraic image is a smooth rational curve. Smoothness is thus proved independently of the weaker distinct-point independence property; the proof does not confuse ordinary center rank with border rank here.

## 5. Explicit example — Section 4, lines 161–200

For r = 3, m = 2, D = 12, direct algebra checks the quotient: z_1 = −5, z_j = −S_j for j != 1, and (Pz)_j = 5(−S_j)−S_j(−5) = 0. The other twelve columns form 5I, so the kernel is precisely the center line. Homogenization to degree 12 is correct for every listed coordinate, including j = 0 and j = 12.

There are no base points. At s = 0 the final coordinate is 5t^12. On s = 1, g_0 = 5−3t forces t = 5/3, whereas g_2 = 5t^2−14t then equals −85/9. This checks the entire parameter line, not a sampled set.

The listed integer coordinates of v are −(1+2^j+3^j) for j in {0,2,...,12}. Differentiating g gives v at zero because the index 1 was removed. Also sum_(a=1)^3 g_j(a) = 5S_j−6S_j = −S_j. Expanding that identity proves the displayed nine-term tensor-square expression.

Independently, the confluent Vandermonde determinant is product_i a_i^2 times product_(i<j)(a_j−a_i) = 36·2 = 72 for a_i = 1,2,3. The determinant of M is (−1)(−1)^3 = 1, so det(H) = 72^2 = 5184, as printed. This exact arithmetic supports smoothness; it is not being used as a replacement for the universal rank lower bound. That lower bound comes from K = 8 and the product lemma, yielding square rank 9.

## 6. Eventual saving — Section 5, lines 202–217

The polynomial q(t) has no constant coefficient and its coefficient of t is v. Therefore q(t)^tensor k has degrees between k and kD and coefficient v^tensor k at t^k. For L = k(D−1)+1 the width of this interval is L−1, so no other exponent in it is congruent to k modulo L. The roots-of-unity filter therefore extracts the required coefficient exactly. No convergence or asymptotic interpolation is needed.

Each q(zeta) is a difference of two representatives of points on X and has rank at most 2 (a zero difference, if it occurred, would only lower the bound). Expanding tensor powers and summing gives rank at most [k(D−1)+1]2^k. For fixed D and r > 2, the exponential (r/2)^k eventually dominates this linear factor. For D = 12 and k = 13 the values are correctly 144·8192 = 1,179,648 < 1,594,323 = 3^13. This verifies the supplementary claim and explains the compatibility with eventual-power submultiplicativity.

## Verification limits and recommended status

The supplied exact-arithmetic verifier checks relevant coordinate identities, Hankel factorization and determinant, representative boundary cases for the annihilator, and finite roots-of-unity index ranges. Its finite checks do not prove the rank lower bound or the all-parameter statements. Those statements pass the independent arguments above. No diagnostic label has been treated as proof, and no claim of having rerun the supplied program is made in this report.

Recommended canonical status, subject to the parent's independent eligibility and publication checks: **Solved — negative**, retaining the original target and permanent ID. The single explicit curve gives border rank 2 < rank 3 but square rank 9 = 3^2, which fully answers the universal yes/no question. The finite-delay theorem is an additional valid strengthening. The versions restricted to Segre varieties or Veronese varieties remain outside this resolution; they are not missing parts of the present canonical target.
