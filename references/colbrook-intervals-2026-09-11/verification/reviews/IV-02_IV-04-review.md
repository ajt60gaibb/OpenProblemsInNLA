# IV-02 and IV-04 independent proof review

Review date: 2026-09-11. The complete joint manuscript and its complete `common.tex` were read, together with the relevant construction and verification code. The proof was checked independently of the package's claimed status and finite test labels. No manuscript or canonical file was edited.

## Verdict and canonical scope

**PASS. Recommend recording IV-02 and IV-04 as resolved by a complexity classification: each requested deterministic polynomial-time exact-output algorithm exists if and only if P=NP.** This does not prove P differs from NP or give an unconditional negative answer to algorithm existence.

The canonical files are `intervals-and-absolute-value-equations/IV-02/README.md` and `IV-04/README.md`. They use independent rational entry intervals for general, not necessarily symmetric, tridiagonal matrices. IV-02 asks for both exact determinant endpoints uniformly in dimension. IV-04 asks for the exact coordinate hull, including empty sets, unbounded coordinates, and singular interval members. The lower bounds apply even to an everywhere nonsingular subfamily with fixed superdiagonal entries one; the solution-hull reduction uses the single right-hand side -e_N and bounded nonempty solution sets. Thus hardness is not obtained by exploiting only the singular or unbounded extension of IV-04.

The manuscript also supplies valid FP^NP upper bounds for the complete canonical outputs, including the exceptional hull cases. Its determinant upper-threshold decision problem is NP-complete. The function problems are NP-hard and in FP^NP; it does not establish a stronger completeness classification for those function problems.

The constructed matrices are nonsymmetric. No separate classification for symmetric tridiagonal intervals is claimed. No strong NP-hardness, fixed-precision hardness, or additive-approximation hardness follows from this small rational-gap reduction. These are limits of the result rather than unhandled cases of the displayed canonical questions. No novelty, authorship, or publication-priority verdict is made.

## Source identities and complete coverage

All paths below are relative to `.cache/colbrook-package-submission/nla_submission/`. Hashes cover the entire UTF-8 file after CRLF-to-LF replacement, without trimming or other changes.

| File | Normalized bytes | SHA-256 |
|---|---:|---|
| `manuscripts/IV-02_IV-04.tex` | 9,912 | `8794ee90e8ac9982384fff220c531ce123a5f29c2bf2abaaf15853b966c4f435` |
| `manuscripts/common.tex` | 985 | `d8e7a0de2ed1a1fd162b147211fe29c7b1d7bfbc0be7b827dcda4d9a2653d0d4` |
| `code/verify_exact.py` | 10,215 | `f7ef316edcb336e64b07372613223c6d96e014a2c338508b86871d73138b549a` |
| `code/nla_algorithms.py` | 7,968 | `47cd54ef30094e0bfa6ffd89ff8678c28d57d35a16f17783b3be0f22488a82a0` |

The audit covers the abstract and scope, the rotation and continuant construction (line 9 onward), equation `eq:cos` (line 55), all separation and regularity estimates (line 60 onward), Theorem 1 `thm:det` (line 87), the corner-cofactor reduction and Theorem 2 `thm:hull` (lines 93–109), and every exact-output upper-bound argument (line 110 onward), plus bibliography and common definitions. `common.tex` supplies standard notation and presentation commands; it contains no hidden substantive hypothesis or proof dependency.

## Independent reduction audit

### Companion products and independent interval embedding: PASS

For M(a,beta)=[[a,-beta],[1,0]], multiplying the two claimed rotation factors gives

\[
M(-s/c,-1/c)M(s,-c)
=\begin{pmatrix}(1-s^2)/c&-s\\s&c\end{pmatrix}
=\begin{pmatrix}c&-s\\s&c\end{pmatrix}.
\]

Here c squared+s squared=1 and c>0. The gate product M(0,-1)M(0,q)=diag(1,-q) also checks directly. For positive integer weights, t_i=w_i/(10W squared)<=1/10, so every c_i is positive and division by c_i is legitimate.

There are N=4m-2 scalar companion layers. Their first coordinate is the determinant continuant of a genuinely tridiagonal N by N matrix with upper diagonal one and subdiagonal beta_j. The first formal beta is irrelevant because p_-1=0, so the missing matrix entry at that location creates no mismatch. Each q_i occurs in one distinct lower-diagonal matrix entry, with its own independent interval [-1,1]. No shared-parameter dependency is imposed on uncertain entries. All other entries are rational singletons, which the canonical targets permit.

At a vertex, the gates are genuine identity/reflection maps, so vector lengths stay one. The angular recurrence gives final angle sum sigma_i theta_i, with sigma_m=1 and sigma_i the product of the subsequent gate signs. Conversely, choosing epsilon_i=sigma_i sigma_(i+1) realizes any such pattern. Simultaneous negation of all signs preserves both a zero signed weight sum and its cosine, so fixing the final sign loses no required case. This establishes the exact determinant expression at every vertex, not merely a numerical rotation approximation.

### Separation, rational threshold, and full-box regularity: PASS

The integral estimate 0<=2t-2 arctan(t)<=2t cubed/3 yields

\[
E\le\tfrac23\delta^3W^3=\frac{\delta}{150W}\le\frac{\delta}{10},
\qquad \delta=\frac1{10W^2}.
\]

The sum of all angles is at most 2 delta W=1/(5W)<=1/5. Every vertex determinant is therefore at least cos(1/5)>0. Multiaffine interpolation writes the determinant at every interior box point as a convex combination of vertex determinants. This proves nonsingularity throughout the interval family; positive vertex determinants alone would not suffice for a general nonlinear map, but the required multiaffinity holds here.

In a yes instance of PARTITION, a signed angle sum has absolute value at most E<=delta/10, and cos(x)>=1-x squared/2 gives maximum determinant at least 1-delta squared/200. In a no instance, every integer signed weight sum has absolute value at least one, so the absolute angle sum is at least 2delta-E>=19delta/10. It is also at most 1/5. On this range cos(x)<=1-x squared/3, giving the upper bound 1-(361/300)delta squared, strictly below 1-delta squared. Thus the rational threshold tau=1-delta squared/2 lies strictly between the cases. Maximizing over the full box is the same as maximizing over its vertices, so no interior point defeats this gap argument.

These inequalities include the m=1 edge case: N=2, there are no uncertain gates, and a single positive weight is correctly a no instance. Singular leading principal minors or zero diagonal entries in intermediate layers do not obstruct the continuant recurrence; the proof never divides by those minors.

### Binary bit model and NP membership: PASS

The input weights are binary integers, and log W is polynomial in their total input length. Each rational c_i,s_i,-s_i/c_i,-1/c_i and tau uses numerator and denominator of bit length O(log W); there are O(m) rows. The construction does not repeat w_i elementary rotations or perform real-number arctangent computations in the reduction. Angles are only used to analyze rationally specified matrices.

The gap can be exponentially small as a real number relative to the binary input length, but its rational description has polynomial length. This is fully adequate for exact threshold hardness. The reduction is a polynomial many-one reduction from PARTITION. For unrestricted rational tridiagonal intervals, a maximizing vertex is a polynomial-size witness for an affirmative threshold instance, and rational determinant evaluation has polynomial bit complexity. This proves NP-completeness of that decision language. The everywhere-regular restriction is correctly stated as a hardness restriction, without relying on a separate promise-verification claim.

### Exact solution-hull transfer: PASS

The inverse entry (T inverse)_(1,N) is cofactor_(N,1)/det(T). Deleting row N and column one leaves a lower-triangular matrix with diagonal equal to the fixed upper-diagonal entries, all one. Thus its determinant is one, and the inverse entry is (-1)^(N+1)/det(T). Since N is even, multiplying by the right-hand side -e_N yields x_1=1/det(T)>0.

The full interval family is compact and all its determinants are uniformly positive, so inversion is continuous and its solutions for the fixed right-hand side form a nonempty compact set. Its lower first-coordinate endpoint is precisely 1/max det(T). It decides the threshold by testing whether that endpoint is at most 1/tau. The reciprocal inequality direction and sign both match the manuscript. Therefore exact hull computation is NP-hard even in the regular bounded case requested by the historical source, as well as in the wider canonical model.

## Exact-output upper bounds: PASS

For determinants, a product of input denominators is already a sufficient common denominator with polynomial bit length; a least common multiple is optional. After scaling entries to integers of absolute value at most H, n!H^n bounds every determinant, and its logarithm is polynomial in the input length. NP vertex-threshold queries allow binary search for exact extremal integers, followed by division by the common denominator to the nth power. The minimum is handled by the corresponding minimum-threshold predicate. Crossing zero and singular members cause no difficulty.

For hulls, rowwise independent interval evaluation gives the exact condition |Cx-b_c|<=R|x|+b_r. For each sign vector s, imposing D_s x>=0 converts this into the two stated systems of linear inequalities. The signs of both R D_s terms are correct. Zero coordinates may belong to either orthant, so no points are excluded. The union of these 2^n rational polyhedra is exactly the united solution set, not an enclosure.

Each sign polyhedron is pointed because it lies in an orthant: its lineality space is zero. A nonempty pointed polyhedron has a vertex, including lower-dimensional cases, and a bounded linear objective attains its optimum at a vertex. After clearing all coefficient and right-hand-side denominators, the same polynomial-size integer bound H works for every sign choice. Cramer's rule gives a uniform Q=n!H^n bound on absolute vertex-coordinate numerators and positive denominators. In particular every finite hull endpoint is rational with polynomial encoding length.

Feasibility can be certified by a sign choice and a polynomial-bit rational vertex. Coordinate unboundedness can be certified by a feasible point and a rational recession direction with the relevant coordinate normalized to plus or minus one. The normalized direction is a feasible rational linear system with polynomial coefficient size, so standard basic-feasible-solution bounds provide a polynomial-size certificate. If a coordinate is unbounded in the finite union, it is unbounded in at least one member. Empty and infinite outputs are therefore detected by polynomially many NP queries.

For a finite upper endpoint, existence of a feasible point with x_i>=t is an NP predicate by the same sign-polyhedron argument after adding that inequality. A bracket within [-Q,Q] of width less than 1/(2Q squared) isolates the endpoint among rationals of denominator at most Q: distinct such fractions differ by at least 1/Q squared. Polynomial-time continued-fraction reconstruction is justified, for example by using the bracket midpoint and the standard convergent criterion, then testing which candidate lies in the bracket. All binary-search rationals have polynomial bit length. The argument for lower endpoints applies to -x_i. Thus the full task, not just its regular instances, lies in FP^NP.

If P=NP these oracles can be replaced by polynomial algorithms; conversely, either requested polynomial exact-output algorithm would decide PARTITION through the reduction. The claimed equivalence is therefore valid, with P versus NP itself left open.

## Code and independent computations

The relevant portions of `nla_algorithms.py` are `partition_tridiagonal`, `continuant`, and the sign enumerator. The code constructs the stated layers using exact SymPy rationals, assigns each gate to one lower-diagonal entry, and leaves every superdiagonal one. Its continuant multiplies the actual two off-diagonal neighbors, which reduces to beta_j in this construction. These implementations match the manuscript.

The relevant `verify_exact.py` functions enumerate signed weights and gate vertices, use Fraction rotations, and compare selected concrete matrix determinants and inverse cofactors. The fresh parent-run [exact_results.json](../exact_results.json) reports 430 PARTITION instances, 15,303 exact gate vertices, and 15 explicit matrix/cofactor checks, all passing. These are finite regression checks, not the hardness proof and not a validation of the general FP^NP hull algorithm.

Independently of the supplied functions, this reviewer used standard-library Fraction Gaussian elimination on all gate vertices for weights [1], [1,1], [1,2,3], [1,3,5,7], and [1,2,8]. The 19 constructed matrices had positive exact determinants, the solved first coordinates equaled the reciprocals of those determinants, and every exact maximum correctly classified the weight instance. This supplies a distinct elimination-based algebra check; the uniform reduction and polynomial bounds were established analytically above.

## Primary-source comparison

Primary interval sources accessed on 2026-09-11:

- [Horacek, Hladik, and Matejka, published determinant paper](https://journals.uwyo.edu/index.php/ela/article/download/1831/1831/1831), Section 5.4, Proposition 5.6 and following paragraph: the established polynomial result concerns interval tridiagonal H-matrices, while general tridiagonal determinant computation is posed as open. The new reduction addresses that general independent-entry problem and does not contradict the H-matrix subclass result.
- [Hladik, overview, arXiv:1711.08732](https://arxiv.org/pdf/1711.08732), Section 2, page 3: exact determinant range and tight tridiagonal-system hull are explicitly listed as separate open tasks. The manuscript supplies separate reductions for them.
- [Horacek, Hladik, and Cerny, complexity chapter preprint](https://arxiv.org/pdf/1602.00349), Section 1.4.3, structured-systems discussion and Theorem 9: the tridiagonal question is distinguished from bidiagonal solvability; the section's boundedness restriction is explicit. The submitted hull hardness already satisfies that restriction.

The reduction invokes the standard NP-completeness of positive-integer PARTITION, cited to Karp's 1972 paper. Attempts to inspect its historical scanned original through university mirrors exceeded the web tool's document-size limit, and the DOI did not load; this review does not claim to have read that full original. This is an established complexity-theory premise, not an unverified submission-specific assertion. All novel reduction calculations and exact-output steps were checked directly.

No substantive gap or required amendment was found. The record should preserve the exact-output, binary-input, nonsymmetric, independent-entry scope and the P=NP qualification.
