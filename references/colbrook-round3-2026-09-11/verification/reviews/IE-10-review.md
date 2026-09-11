# Independent proof review: IE-10

Date: 2026-09-11. Verdict: **PASS for the complete claimed mathematical scope.** Recommended canonical status: **Solved**, affirmative, with universal constants `C=1700`, `c=3` for the exact complex-sphere cyclic-shift model. Both supplied probability arguments pass independently after their common deterministic lemmas. No source correction is required.

## Source identity and target

I read the complete TeX and Markdown manuscripts, including the explicit example, limitations, and sources, and compared the actual `eigenvalues-and-inverse-problems/IE-10/README.md`. Full-source SHA256 values use complete UTF-8 text, CRLF replaced by LF, with no trimming:

| Source under `.cache/colbrook-round3/nla_round3_submission/manuscripts/` | SHA256 |
| --- | --- |
| `IE-10-proposed-resolution.tex` | `9fe78337c71646b3e9de33810af4b2985d24023aeac00e3f4c8008700c5ad5a2` |
| `IE-10-proposed-resolution.md` | `82c98671364bc70684e387c52f05125d22ec0ee5fe89382bc6212b76f4a22eba` |

The TeX is standalone, without a common proof input. Its mathematical content agrees with the Markdown. Locators below refer to TeX lines: Theorem 1 at 87; the model at 112; conjugation at 157; derivative identity at 178; Lemma 2 at 192; Lemma 3 at 213; conditional pencils at 230; Proposition 4 at 271; Lemma 5 at 318; expectation argument at 366; Corollary 6 at 390; diagnostics and exact example at 398.

The canonical target asks for the same constants for every integer `n>=3` and `2<=k<n`, with randomness only in a uniform complex unit starting vector. Its condition number is the infimum over eigenbases, measured in an orthonormal basis of the Krylov subspace, and is infinite for a nondiagonalizable compression. Theorem 1 uses precisely these conventions. The proof neither replaces the Krylov subspace by an independent Haar subspace nor claims a deterministic bound for every starting vector.

## Primary-source check

I accessed [Amsel et al., workshop report v3, Section 3.3, Problem 3.5](https://arxiv.org/html/2602.05394v3#S3.SS3) on 2026-09-11. The report explicitly singles out the circulant shift within its broader conditioning question. Its August 20 update describes a nonnormal diagonalizable obstruction with real Gaussian starts and leaves the normal-input restriction unresolved there. Thus that obstruction does not contradict this manuscript's model. The report also distinguishes Haar-subspace results from Krylov results. This check verifies the motivating problem and scope; it is not an exhaustive literature-priority search and does not attribute this proof to that source. The manuscript's statements about its unreviewed status describe its state at submission; this record supplies subsequent independent agent review, not external peer review or formal verification.

## Common deterministic argument

**Weighted model.** Fourier diagonalization is unitary, so the starting vector remains uniform complex spherical. Independent standard complex Gaussian spectral coordinates have independent mean-one exponential squared moduli. Dividing all weights by their sum leaves the compression unchanged, while coordinate phases are removed by a unitary that commutes with multiplication by the nodes. The polynomial evaluation model is therefore exactly isometric to the Krylov model. Positive weights and the Vandermonde rank give dimension k, almost surely. The coefficient matrix is `G^-1 F`, but its norm is measured with metric G; the proof consistently converts to orthonormal coordinates when using ordinary matrix norms.

**Matched left/right vectors.** On unit-circle nodes, `Jf(zeta)=zeta^(k-1) conjugate(f(zeta))` is an antiunitary involution. It reverses the coefficients of polynomials of degree below k, hence preserves that subspace and its orthogonal complement. It commutes with the orthogonal projection and conjugates multiplication by z to its adjoint. Therefore `JH J=H*`, and `ell=Jr` is a unit left eigenvector with exactly the same weighted coordinate magnitudes as r. For a simple eigenvalue the left/right pairing is nonzero and its reciprocal modulus is the norm of the rank-one spectral projector.

**Derivative identity, including the varying metric.** In coefficient coordinates the left vector satisfies `ell* F=lambda ell* G`. Differentiating `Fr=lambda Gr` and multiplying by `ell*` cancels the derivative of r. The derivative is `ell*(F'-lambda G')r/(ell*Gr)`. Since the two derivatives are the same rank-one evaluation matrix multiplied respectively by zeta and 1, the formula in Section 3.2 follows. This derivation explicitly accounts for the varying Gram matrix; it does not incorrectly differentiate a fixed-metric compression. Taking absolute values and using the matched magnitudes gives equation (6).

**Sensitivity bound.** The summands of the pairing have moduli `p_j` with sum one. Hence `|alpha|>=2 max(p_j)-1`. When the individual projector norm exceeds 2, each mass is below 3/4. Separation d allows at most one node within distance strictly below d/2 from the eigenvalue; the remaining mass is at least 1/4 and supplies weighted mean distance at least d/8. Equation (6) then proves Lemma 2, including the case of a node exactly at distance d/2. For projector norm at most 2 the other branch of the maximum applies.

**Balanced eigenbasis.** With unit right eigenvectors in R, the dual row norms of `R^-1` are precisely the projector norms `kappa_i`. Scaling column i by `sqrt(kappa_i)` makes the squared Frobenius norms of both the scaled matrix and its inverse equal to `sum_i kappa_i`. Their spectral-norm product is at most that sum. This proves the bound for the infimum over eigenbases used in the canonical definition.

## Simplicity and conditional algebra

The discriminant is a complex-coefficient polynomial in real weights. It is nonzero because weights supported on exactly k distinct nodes give an invertible Vandermonde evaluation matrix and a compression similar to a diagonal matrix with distinct eigenvalues. This boundary witness suffices to show that the polynomial is not identically zero; its zero set on the positive real orthant has measure zero. At least one coefficient in each univariate conditional discriminant is a nonzero polynomial of the remaining weights, so exceptional conditionings also form a null set.

Because `k<n`, the remaining n-1 positive nodes give `G_0>0` after any single weight is removed. Rank-one determinant multilinearity gives `p(z,t)=p_0(z)+t p_1(z)`. Its coefficients are affine in t and the degree-k discriminant is homogeneous of total coefficient degree `2k-2`, so the claimed bound on the number of complex discriminant zeros holds. On positive real t, the leading coefficient is positive and the compression is a contraction. Thus only finitely many positive t can be collisions for any nonexceptional conditioning. These facts justify the almost-sure simple-spectrum uses in both proofs.

## First probability proof: Proposition 4

The exponential density is at most one. Excluding `t_0<=2 epsilon` and the intersections with disks of radius `2 epsilon` around at most `2k-2` discriminant zeros costs at most `8k epsilon` for one conditioned coordinate. Fubini and the union bound over n coordinates give the asserted `eta/2` for `epsilon=eta/(16nk)`; no independence of these bad events is needed.

In the good disk `|t-t_0|<epsilon`, the Hermitian part of G(t) is positive definite because `Re t>0`. Hence its leading coefficient never vanishes. Together with the nonzero discriminant and simple connectedness of the disk, this gives holomorphic root labels on the entire disk, not just near its center. For any corresponding nonzero eigenvector x, `g=x*G_0x>0`, `|m|=|x*F_0x|<=g`, and `s=|ax|^2>=0`. The denominator obeys `|g+ts|>=g+(Re t)s`; the numerator is at most `g+|t|s`. These inequalities give `|z|<=3` throughout the disk. Cauchy's estimate, first on smaller radii and then by a limit, gives `|lambda_i'|<=3/epsilon`.

Markov gives `W<=2n/eta` except with probability `eta/2`. On the joint event, Lemmas 2 and 3 give at most `768 n^2 k^2/(d eta^2)`. This bound also dominates the alternative `2k`. For cyclic nodes `d=2 sin(pi/n)>=4/n`, so the result is `192 n^3 k^2/eta^2`. At eta=0.01 this is at most `1,920,000 n^5`, which is below the stated `2,000,000 n^5`. Thus Proposition 4 alone proves the canonical existence assertion for every admissible pair, independent of Lemma 5.

## Second probability proof: root-locus variation and expectation

The crucial count in Lemma 5 bounds parameter preimages, so it does control traversed length rather than merely the image of the curve. For a moving root outside common zeros, its position determines its unique parameter `t=-p_0(z)/p_1(z)`. At a simple parameter that position belongs to one root. The nonzero real polynomial `q(x,y)=Im(p_0(x+iy) conjugate(p_1(x+iy)))` has degree at most 2k. For all but finitely many vertical lines its restriction is a nonzero polynomial, hence contains at most 2k possible moving-root positions; the same holds for horizontal lines. Thus those line intersections have at most 2k parameter preimages across all roots and all simple intervals.

If q is identically zero, the rational function `p_0/p_1` is holomorphic and real valued off finitely many poles, so it is constant. Its roots then stay constant for positive t because the leading coefficient does not vanish. The case `p_1=0` is also constant. A common root of p_0 and p_1 is a constant branch; another branch can meet it only at a collision, already excluded. Lines containing constant-coordinate arcs form an exceptional null set and contribute zero variation in that coordinate.

On every simple interval, each coordinate of a root is real analytic. Unless constant, its derivative zeros are isolated, permitting countably many monotonicity intervals. Change of variables on those intervals and Tonelli convert the preimage counts to total real-coordinate variation at most `4k`, and separately imaginary-coordinate variation at most `4k`, since all roots are in the unit disk. This also handles possible unbounded derivatives near collisions or endpoints without assuming integrability in advance. The sum of complex arclength integrals is therefore at most `8k`. All parts of Lemma 5 pass.

Conditioning on weight j, `t exp(-t)<=1` now bounds the expected weighted sum of root speeds by `8k`. Summing over coordinates and applying the deterministic bounds gives `E kappa_V<=2k+64nk/d`. All terms are nonnegative, so Tonelli is applicable before finiteness is established. Exceptional spectra and conditionings are null; assigning infinite condition number there does not change the Lebesgue expectation. For cyclic nodes this is at most `2k+16n^2k<=17n^2k` for n>=3. Markov and `k<n` give `P{kappa_V<=1700 n^3}>=0.99` with the same constants for every n and k, as requested.

Corollary 6 also passes: with one common random start, the expectation of the sum over k is bounded by `(17/2)n^4`. Markov on that sum bounds every summand simultaneously by `17n^4/(2eta)` with probability at least `1-eta`. No independence between compressions is invoked or needed. This simultaneous statement is stronger in quantifier type but uses a different n exponent from the pairwise canonical bound.

## Exact example, verification limits, and final scope

I independently checked the algebra of the n=3, k=2 example: its determinant is the displayed quadratic multiplied by 3, and its discriminant is `81(t-1)(t+1/3)`. At t=1 the compression has a repeated defective zero eigenvalue. For `0<t<1`, the two conjugate roots satisfy `|z+1|=1`; their angles about -1 move from plus/minus pi/3 to zero. For t>1, solving for t gives `(z^2+z+1)/(-2z^2+z+1)` with derivative `3z(z+2)/(2z^2-z-1)^2`. Its signs give the stated real branches and total length `2pi/3+3/2`. This verifies the diagnostic example analytically, without extrapolating it to the general lemma.

The accompanying numerical diagnostics were not relied on to establish probability, generic simplicity, conditioning, or curve-length claims. This review does not certify their implementation or finite-precision eigenvector computations. No finite sample could replace either analytic probability proof.

No case of the exact canonical target remains unresolved by the supplied proof. The arbitrary-distinct-unit-circle-node extension is valid with its explicit separation dependence `1/d`; it does not yield a node-independent polynomial bound for every normal input. Real-sphere starting vectors, unrestricted nonnormal inputs, the general workshop pseudospectral-area question, and finite-precision construction of an eigenbasis remain outside the claims reviewed here. No priority or human authorship inference is made. No manuscript or canonical file was changed during this review.
