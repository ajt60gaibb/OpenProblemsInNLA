# Independent agent review of the complete RA-10 proof

**Verdict: PASS for the full canonical RA-10 statement, with universal constant C=11.** I found no mathematical gap or missing hypothesis in the exact manuscript identified below. No mathematical correction is required for this verdict.

Reviewer: the separate Codex agent `/root/review_aa01`. Review completed on 11 September 2026. This is independent agent review, not external human peer review or formal verification. The reviewer independently reconstructed the new compression calculation and the constant bookkeeping before reading the integrated manuscript, then audited the integrated version against the canonical target. Earlier exploratory work on a different, unproved square inequality is not used here.

## Exact versions reviewed

- Manuscript: `/tmp/nla-remaining-round3/ra10/full-proof-candidate.md`, 11,521 bytes. SHA-256: `eaf566e469e1c3a5a21473852c29247d86e7960f87178d0245ea7f89379e8e35`.
- Canonical target read from `/tmp/nla-ra12-worktree/randomized-and-low-rank-approximation/RA-10/README.md`, 5,101 bytes. SHA-256: `31dbcd71f6840365aee2b98733979cfe7156222b2e5e5ede5539f42a1626449c`.
- External integral representation checked directly in [Chansangiam, arXiv:1304.7936v1](https://arxiv.org/pdf/1304.7936v1), Proposition 1.1, printed page 2. The statement gives a finite positive measure on the compactified half-line and the kernel x(1+s)/(x+s). The manuscript correctly separates its endpoint atoms and changes the interior measure.
- The source question was also checked against [Persson, Meyer and Musco, arXiv:2311.14023v2](https://arxiv.org/html/2311.14023v2), Section 1.2. The target concerns a fixed loss in relative approximation accuracy after removal of matrix ordering.

The verdict binds the complete mathematical argument in this version. A later mathematical edit requires another check; a faithful typesetting or metadata conversion can be checked by an explicit addendum.

## Scope check

Theorem 1 proves the requested implication for every real symmetric PSD pair A and Ahat, every n>=2 and 1<=k<n, every epsilon>=0, and every continuous nonnegative operator-monotone function on the nonnegative half-line. The constant 11 is independent of all these quantities. The proof retains the rank-k projection selected from an arbitrary ordered eigenbasis of Ahat, including choices within repeated eigenspaces and choices containing zero eigenvalues. The two truncations use the same selected vectors.

No step introduces A>=Ahat, commutation, a strict eigenvalue gap, invertibility of A, rank exactly k for the approximant, or uniqueness of the selected eigenspaces. Only the nuclear norm is claimed. Neither the earlier isospectral ridge inequality nor the earlier square inequality is an assumption or conclusion. Sharpness of 11 is not claimed.

## Compression lemma: independent reconstruction

Write A in the selected block decomposition as [H,E; E^T,F], put C=diag(H,0), and first assume H>0. For a unit positive eigenvector v=(u,w) of Z=f_s(C)-f_s(A), with eigenvalue lambda, the strict bound f_s(C)<I and positivity of f_s(A) give 0<lambda<1. Thus mu=lambda/(1+lambda) lies in (0,1/2).

I checked both resolvent block equations. In particular, the first is

    Ew=-mu(sI+H)u.

After division by 1+lambda, the coefficient multiplying E^T in the second row is

    (1-mu)s(sI+H)^(-1)+mu I
      =(sI+mu H)(sI+H)^(-1).

This verifies equation (3), including the factor mu. Taking its inner product with w and substituting the first equation gives exactly

    w^T Fw=mu s(||u||^2-||w||^2)+mu^2 u^T H u.

The Schur inequality F>=E^T H^(-1)E then gives

    ||w||^2 <= (1-2mu)||u||^2-mu s u^T H^(-1)u.

Using ||u||^2+||w||^2=1 yields the lower bound in equation (5). Independently expanding the quadratic form of D=C-A gives

    v^T Dv=mu s+mu(2-mu)u^T H u,

so the sign of the off-diagonal contribution and the coefficient in equation (6) are both correct.

For Delta=(cI-H)_+, the spectral inequality H>=cI-Delta is valid for arbitrary c>0. The difference between the scalar lower bound obtained from (5)-(6) and lambda(s+c)/2 is

    mu [s(1-2mu)+c(1-mu)]/[2(1-mu)],

which is nonnegative. This checks equation (7) without any unmentioned lower bound on H.

Summation over an orthonormal basis of the positive eigenspace is valid even for repeated positive eigenvalues. The P-components satisfy sum uu^T<=I. The coefficients mu(2-mu) lie between zero and one, so their total Delta contribution is at most tr Delta. Also tr(QD)<=tr(D_+) for the positive-eigenspace projection Q of Z. These facts prove Lemma 2 with precisely the factor 2.

The singular-H extension is sound: A+rP stays PSD, its compression is C+rP, its leading block is positive definite, and the difference C-A stays fixed. Ridge functions and positive-part traces are continuous in this finite-dimensional limit. The arbitrary comparison parameter c is held fixed. Consequently the limit establishes the same bound when H is singular; there is no hidden pseudoinverse or range assumption.

## Matching the leading eigenvalues and checking constants

For tau>0, a_k=c is positive. The compression eigenvalue bounds 0<=h_i<=a_i follow from the min-max principle, including ties. If L=sum_(i<=k)a_i-tr H and R=||B0-C||_*, then pinching A-B0 gives

    ||A-B0||_* >= R+tr F = R+tau+L,

which is exactly e0>=R+L. The trace-positive-part identity gives eC=L+2tr(C-A)_+, with the displayed sign as written. The compression defect d is at most L, and the scalar ridge identity bounds the corresponding function trace defect L_s by gL.

Consequently Lemma 2 implies

    ||f_s(A)-f_s(C)||_*-tau_s <= g(2eC+3L).

The noncommuting resolvent product on the selected subspace has norm bounded by gR: one inverse factor is bounded by 1/(s+c), the other by 1/s, and the front factor is s. The nuclear-norm ideal inequality applies without commutation. Both sides of the function difference vanish on the complementary subspace because f_s(0)=0.

The two triangle inequalities and pinching then give

    e_s(B0) <= g(2eC+3L+R)
             <= g(2e0+3R+3L)
             <= 5g e0.

For an arbitrary selected B, the ordered eigenvalue perturbation inequality in the nuclear norm gives r+tau<=||A-B||_*, hence r<=e(B). There is no ordering assumption between A and B in this standard eigenvalue inequality. Replacing the selected eigenvalues by a_1,...,a_k in the same eigenvectors yields e0<=e(B)+r. The two replacement matrices commute with each other, so their ridge difference has nuclear norm at most gr by the scalar identity. Thus

    e_s(B)<=5g(e(B)+r)+gr<=11g e(B).

Finally, a_i<=c for every tail eigenvalue implies tau_s>=g tau. This is the correct direction for converting absolute excess into relative excess. The derived constant is exactly 11; no dimension, spectral condition number, or ridge parameter is hidden in it.

## Integral representation and boundary cases

The cited representation gives f(x)=alpha+beta x+integral x/(s+x) dnu(s) with nonnegative alpha, beta and measure nu. Its endpoint atom at zero gives the constant alpha=f(0), its endpoint atom at infinity gives beta, and the change dnu=(1+s)dm on the interior gives the stated integrability. The canonical real-symmetric definition gives the usual complex-Hermitian matrix definition by realification; continuity supplies the standard extension used in the representation theorem.

For completeness, the elementary estimate

    x/(s+x) <= max(1,x)/(1+s),  x>=0, s>0,

directly shows integrability at each fixed eigenvalue. Thus all finite-dimensional matrix integrals used in the manuscript converge absolutely. The triangle inequality may be applied to their differences. Tail traces are positive linear combinations of the scalar tails. The same ridge constant applies before integration, the linear part has constant one, and the constant part contributes exactly alpha(n-k). This proves the integral step for arbitrary allowed f, including unbounded functions, the zero function and functions with f(0)>0.

The selected functional calculus f(B)_P is essential and is handled correctly: if B has selected zero eigenvalues, f(0) is still retained on those selected directions, while it is removed on ker(P). This is exactly f(Ahat)_k under the canonical convention. When tau=0 the input premise forces A=B, independent of epsilon. Since A is supported on P, the output error is f(0)(I-P), with nuclear norm (n-k)f(0), exactly the optimal tail. This covers all zero-tail and rank-deficient endpoints without dividing by zero. If tau>0 but the transformed tail is zero, the integrated bound still applies without division by that tail.

## Review conclusion

The argument proves the full existential-constant question of RA-10 with C=11. The new mathematical step is the compression estimate in Lemma 2; its proof and the subsequent reductions are valid in the exact stated scope. No numerical experiment is needed for this conclusion. This report does not audit publication priority, the current open status of every branch or fork, PDF layout, or any separate lower-bound claim from another manuscript. Those are separate submission checks.
