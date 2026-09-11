# MF-15 independent proof review — 2026-09-11

**Verdict: PASS for the submitted partial result; the full canonical target remains partially resolved.** The manuscript proves CE_n>=2n-4 for every n>=3, using rational nonnegative matrices with simple positive spectra. In combination with the cited upper bound it proves CE_4=4. It does not prove the necessary upper bound CE_n<=2n-4 for n>=5, so the all-dimensional equality in MF-15 must not be marked resolved. No material gap was found in the theorems actually claimed.

This is an independent Codex mathematical audit. The complete manuscript, its accompanying finite certificate code, the canonical target, and the primary source were read. Attached verification labels were not accepted as proof. No original manuscript or canonical file was changed; publication and priority are not certified by this review.

## Source identity and locators

The source reviewed was `.cache/colbrook-research-submission/nla_research/submission/MF-15/manuscript.tex`, including its complete standalone preamble and bibliography. SHA256 means the **complete original UTF-8 text with CRLF changed to LF, no trimming and no final-newline removal**, re-encoded as UTF-8.

| Input | Normalized bytes | SHA256 |
| --- | ---: | --- |
| Complete MF-15 manuscript | 10869 | `4ef08c7bca6c059fe84705d13c88eaa3bbf783d645aef5ab498e9f309582e364` |
| Canonical `matrix-functions-and-stability/MF-15/README.md` before the update | 3221 | `4e914889293945ee2e11eb464ea6eee41b8b661d6cf3d2f9348c39a337e21d8c` |

| Claim | Original manuscript locator | Verdict |
| --- | --- | --- |
| Universal lower bound, with rational examples | Theorem 1, `thm:lower`, line 22 | PASS |
| Matrix family and permitted parameter range | `eq:matrix`, line 34; `eq:epsrange`, line 47 | PASS |
| Positive simple eigenvalues and their limits | Lemma 2, `lem:roots`, line 63 | PASS |
| Resolvent and spectral power entry | `eq:resolvent`, line 104; `eq:power`, line 111 | PASS |
| Scaled negative-entry limit | Lemma 3, `lem:limit`, line 117 | PASS |
| CE_4=4 | Corollary 4, `cor:ce4`, line 162 | PASS |
| All-dimensional equality CE_n=2n-4 | Canonical target | Not proved for n>=5 |

## Exact target and primary-source comparison

The canonical class is the nonsymmetric class of entrywise nonnegative diagonalizable real matrices with nonnegative real eigenvalues, and the operation is conventional spectral powering. The manuscript uses precisely this class and operation. Its simple positive-spectrum examples are admissible members of that class. Restricting to this subclass is sufficient for a lower bound on the universal critical exponent, but cannot establish an upper bound for the whole class.

[Han–Johnson–Paparella v3, Theorem 3.3](https://arxiv.org/html/1407.7059v3) gives CE_n<= (n^2-2n)/2 for even n and CE_n<= (n^2-3n+4)/2 for odd n. Their Corollary 4.5 gives CE_3=2, Conjecture 4.6 asks for CE_4=4, and Question 4.7 asks for the general linear formula. Thus the cited upper bound really yields four at n=4. The submitted lower bound addresses Question 4.7 in one direction, beyond the source's finite examples. Neither symmetric doubly nonnegative results nor Hadamard-power results supply its missing upper bound.

## Matrix and characteristic polynomial

Put m=n-2>=1. The family has m small diagonal entries i epsilon, the two large diagonal entries 1 and 2, m successive off-diagonal edges of weight epsilon, one edge of weight one, and the wraparound edge kappa=1/4. All entries are nonnegative. For rational epsilon all entries are rational.

In the determinant of zI-A, any choice of one off-diagonal cyclic edge forces all edges of that full cycle. Thus the only permutation terms are the full diagonal product and the full cycle. The product of the n negative off-diagonal entries and the sign (-1)^(n-1) of the cyclic permutation is negative in every dimension. Its magnitude is kappa epsilon^m. This proves

`p_epsilon(z) = product_(i=1)^m(z-i epsilon)(z-1)(z-2)-kappa epsilon^m`.

There is no hidden parity restriction on n.

## All eigenvalues positive, distinct and controlled

The low-root rescaling q_epsilon(u)=epsilon^(-m)p_epsilon(epsilon u) is exact. At u=i+-1/4, one factor in product_j(u-j) has magnitude 1/4, at most one other has magnitude below one, namely 3/4, and the rest exceed one. The absolute product is at least 3/16; for m=1 it is 1/4. Across the interval its sign changes because only the factor u-i changes sign.

The full allowed range epsilon<=1/[8(m+1)] implies `epsilon(i+1/4)<1/8`. Hence both extra factors are positive and their product exceeds 105/64. The signed product before subtracting kappa has magnitude greater than 315/1024>1/4. Subtracting 1/4 preserves each endpoint sign, leaving opposite signs. This establishes one positive root in each of the m disjoint low intervals. The argument is valid at the stated closed upper endpoint of the epsilon range.

At z=1 and z=2, p is strictly negative. At z=3/4, all factors z-i epsilon exceed 5/8, so

`p(3/4) > (5/16)(5/8)^m-(1/4)epsilon^m >0`.

For the last inequality it suffices that epsilon<=1/16: the ratio of the first positive term to the subtracted term is at least `(5/4)10^m>1`. At z=9/4 the product of the two large factors is again 5/16, while each small factor exceeds 17/8; the same argument gives strict positivity. There is therefore a root in (3/4,1) and another in (2,9/4).

The m low intervals lie below 1/8 and are separated from both high intervals. There are now m+2 disjoint intervals containing roots of a degree-(m+2) polynomial. Each root must be simple and there can be no remaining real or complex roots. This proves diagonalizability and the claimed positive simple spectrum on the entire parameter range, not only asymptotically.

At epsilon=0 the low polynomial has degree m and the same endpoint signs; it likewise has exactly one simple root in each low interval. Coefficient convergence of q_epsilon and boundedness of each rescaled root force every subsequential limit to be that unique root. Thus the stated convergence u_i(epsilon)->u_i follows without assuming analyticity of the roots. Applying the same compactness reasoning to p_epsilon(z)->z^m(z-1)(z-2) forces the two high roots to converge to 1 and 2 respectively.

## Resolvent and fractional-power expansion

The (1,m) resolvent entry follows either from its cofactor or from the forced directed path from 1 to m: the m-1 epsilon edges contribute epsilon^(m-1), and the unvisited large-diagonal vertices contribute (z-1)(z-2). For m=1 it is the (1,1) diagonal cofactor, with empty path product one. Thus the formula covers n=3.

Because every eigenvalue is simple, the residue of this entry at a root lambda is exactly `epsilon^(m-1)(lambda-1)(lambda-2)/p_epsilon'(lambda)`. The resolvent residues are the spectral projectors of the diagonalizable matrix. Multiplying them by lambda^alpha yields the stated conventional-power formula for each real alpha>0. No positive-entry property of the projectors is assumed, and no branch ambiguity arises since all eigenvalues are positive.

## The asymptotic limit and its quantifiers

For a low root lambda_i=epsilon u_i(epsilon), differentiating the rescaled polynomial gives `p_epsilon'(epsilon u)=epsilon^(m-1)q_epsilon'(u)`. The coefficient of lambda_i^alpha in the spectral expansion therefore equals

`(epsilon u_i-1)(epsilon u_i-2)/q_epsilon'(u_i)`.

Its denominator converges to the nonzero derivative of the simple limiting root, so the coefficient is bounded. The root is O(epsilon), and for fixed alpha the total low-root contribution is O(epsilon^alpha). It vanishes after scaling by epsilon^(-(2m-1)) exactly under the asserted hypothesis alpha>2m-1.

At either high root the characteristic equation gives the exact identity `(lambda-1)(lambda-2)=kappa epsilon^m/Q_epsilon(lambda)`. Consequently its scaled spectral contribution is `kappa lambda^alpha/[Q_epsilon(lambda)p_epsilon'(lambda)]`. At the root tending to b in {1,2}, Q_epsilon tends to b^m and the derivative tends to b^m(b-c), with c the other root. The sum of the two limits is therefore

`kappa[-1+2^(alpha-2m)]`.

This proves Lemma 3, including m=1. For each fixed alpha in (2m-1,2m), the limit is strictly negative, so that entry is negative for every sufficiently small positive epsilon. Epsilon may depend on n and alpha. Uniformity as alpha approaches the endpoints is neither proved nor required.

For any proposed threshold c<2m, choose alpha in `(max(c,2m-1),2m)`, then choose a sufficiently small rational epsilon in the permitted range. This is an admissible counterexample at exponent alpha>c. Hence no such c has the canonical universal property, which proves CE_n>=2m=2n-4. The theorem does not claim an individual fixed matrix with negativity for every alpha in that interval, or strict negativity at alpha=2m.

## Finite interval computations

I read the complete `code/gdn_certificate.py` implementation. It computes the characteristic polynomial and its derivative using rational arithmetic, verifies n disjoint positive sign-changing brackets, and checks the allowed epsilon range. Since the polynomial degree is n, the brackets account for all roots. Its power evaluation uses the exact characteristic identity at every root, avoiding subtraction of nearly equal high-root terms.

At alpha=2m-1/2, the normalized entry is `kappa sum lambda^alpha/[Q_epsilon(lambda)p_epsilon'(lambda)]`. The code uses `lambda^(2m-1)*sqrt(lambda)`, matching that exponent. Rational interval products use all endpoint products; division rejects intervals containing zero. Square roots are enclosed by integer-square-root floors and an upper endpoint increased by one scaled unit. Outward decimal rounding preserves inclusion. The printed floating-point approximations are used only for display, not for negativity certification.

I inspected the fresh rerun log `.cache/colbrook-research-submission/logs/gdn_certificate.py.log` and the diagnostics record: supplied results matched exact verification, regeneration passed, and all eight intervals for n=3,...,10 had negative upper endpoints. Their rounded values agree with the manuscript table. These executed finite certificates support the examples; the all-dimensional result rests on the preceding analytic proof, not on extrapolation from those examples.

## Status recommendation

**Retain canonical status: Partially resolved.** Record the proved universal lower bound CE_n>=2n-4 and the newly settled case CE_4=4. The n=3 equality was already known. The precise remaining question is whether CE_n<=2n-4 for every n>=5, or whether a counterexample to that upper bound exists. No resolution of that remaining target is supplied. No small proof fix is needed.
