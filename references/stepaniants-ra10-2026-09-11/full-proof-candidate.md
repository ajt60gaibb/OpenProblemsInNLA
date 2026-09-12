# RA-10: constant-loss nuclear-error transfer without matrix ordering

George Stepaniants  
Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.  
11 September 2026.

**Research proof candidate.** This manuscript was developed with substantial ChatGPT/Codex assistance. Independent mathematical review is pending. It is not a claim of external peer review, formal verification, historical priority, or an optimal constant.

## 1. Statement and notation

For a real symmetric matrix M, write M_+ for its positive part and ||M||_* for its nuclear norm. If P is an orthogonal projection and B=PBP is positive semidefinite, write f(B)_P for the matrix obtained by applying f on range(P) and setting its action on ker(P) to zero. In particular, f(B)_P=f(B) when f(0)=0. The selected projection P is retained even when B has rank smaller than rank(P).

**Theorem 1.** The exact statement of RA-10 holds with the universal constant C=11. More explicitly, let n>=2, 1<=k<n, A and Ahat be real symmetric positive semidefinite matrices, and choose any ordered orthonormal eigenbasis of Ahat. Let P project onto its first k vectors and let B=Ahat_k. For every continuous operator-monotone f:[0,infinity)->[0,infinity) and epsilon>=0,

    ||A-B||_* <= (1+epsilon) ||A-A_k||_*

implies

    ||f(A)-f(Ahat)_k||_* <= (1+11 epsilon) ||f(A)-f(A)_k||_*.

Both truncations of Ahat use the same selected eigenvectors. No matrix ordering, commutation, invertibility, spectral simplicity, or strict gap at k is assumed.

Put a_1>=...>=a_n>=0 for the eigenvalues of A and tau=sum_(i>k) a_i. The quantity

    e(B)=||A-B||_*-tau

is nonnegative by the best-rank-k approximation property of the nuclear norm. We first prove the estimate for the ridge atoms f_s(x)=x/(s+x), s>0. The proof only uses finite-dimensional matrix algebra, standard eigenvalue comparison, and the positive integral representation of operator-monotone functions.

## 2. A compression estimate for ridge functions

**Lemma 2.** Let A>=0, let P be an orthogonal projection of rank k, and put C=PAP. Let H be the restriction of C to range(P). For arbitrary s,c>0, set

    D=C-A,   d=tr(c I_k-H)_+,   g=1/(s+c).

Then

    tr(f_s(C)-f_s(A))_+ <= 2g [tr(D_+)+d].                 (1)

This lemma does not require the eigenvalues of C to match any eigenvalues of A.

**Proof.** First suppose H>0. In the orthogonal decomposition range(P) plus ker(P), write

    A = [ H  E ],      C = [ H  0 ].
        [ E^T F ]          [ 0  0 ]

Positivity of A gives F>=E^T H^(-1)E. Put Z=f_s(C)-f_s(A). Let v=(u,w) be a unit eigenvector of Z with positive eigenvalue lambda. Since 0<=f_s(A) and f_s(C)<I, we have 0<lambda<1. Define

    mu=lambda/(1+lambda),     0<mu<1/2.

The resolvent identity Z=s[(sI+A)^(-1)-(sI+C)^(-1)] and Zv=lambda v give

    (sI+A)^(-1)v=(sI+C)^(-1)v+(lambda/s)v.

Multiplying by sI+A and using the two block rows yields

    E w = -mu(sI+H)u,                                      (2)

    E^T (sI+mu H)(sI+H)^(-1)u+(F+mu s I)w=0.              (3)

Taking the inner product of (3) with w and substituting (2) gives

    w^T Fw=mu s(||u||^2-||w||^2)+mu^2 u^T H u.             (4)

On the other hand, the Schur-complement inequality and (2) give

    w^T Fw >= mu^2 u^T(sI+H)H^(-1)(sI+H)u
             = mu^2 u^T H u+2mu^2 s||u||^2
               +mu^2 s^2 u^T H^(-1)u.

Comparing with (4), and dividing by mu s>0, proves

    ||w||^2 <= (1-2mu)||u||^2-mu s u^T H^(-1)u.

Because ||u||^2+||w||^2=1, it follows that

    ||u||^2 >= 1/[2(1-mu)].                                (5)

A direct calculation from (2) and (4) gives

    v^T Dv = mu s+mu(2-mu)u^T H u.                         (6)

Let Delta=(c I_k-H)_+, so H>=c I_k-Delta. By (5)-(6),

    v^T Dv >= mu s+mu(2-mu)c/[2(1-mu)]
                     -mu(2-mu)u^T Delta u
             >= lambda(s+c)/2-mu(2-mu)u^T Delta u.         (7)

The second inequality follows because the difference between its two scalar terms is

    mu [s(1-2mu)+c(1-mu)]/[2(1-mu)] >=0.

Take an orthonormal basis of the positive eigenspace of Z and sum (7). For its orthogonal projection Q, the variational formula tr(D_+)=max_(0<=R<=I) tr(RD) gives tr(QD)<=tr(D_+). Also 0<mu(2-mu)<1 for each positive eigenvalue, and the P-components u of these orthonormal vectors satisfy sum u u^T<=I_k. Therefore

    (s+c) tr(Z_+)/2 <= tr(D_+)+tr(Delta).

This is (1).

If H is singular, apply the proved case to A_r=A+rP and C_r=C+rP, r>0. Their difference remains D, and A_r>=0. For fixed s>0, all resolvents and positive-part traces are continuous as r decreases to zero, and tr(cI-H-rI)_+ tends to d. Taking that limit proves (1) without an invertibility assumption. QED.

## 3. Matching the leading spectrum

Assume tau>0, so c=a_k>0, and continue to write g=1/(s+c). Let B0 be any positive semidefinite matrix supported on a rank-k projection P, whose eigenvalues on that subspace are a_1,...,a_k. Its eigenvectors are arbitrary. Define

    e0=||A-B0||_*-tau,
    C=PAP,  H=C restricted to range(P),
    L=sum_(i<=k) a_i-tr H,    R=||B0-C||_*.

The compression eigenvalues h_1>=...>=h_k satisfy 0<=h_i<=a_i by the min-max principle. Thus L>=0. Pinching A-B0 into the P and I-P blocks cannot increase its nuclear norm, and the complementary A block is positive semidefinite. Consequently

    e0 >= R+L.                                             (8)

Put eC=||A-C||_*-tau. The triangle inequality gives

    eC <= e0+R.                                            (9)

The trace identity ||M||_*=2tr(M_+)-tr M for symmetric M, applied to C-A, gives

    eC=L+2tr(C-A)_+.                                      (10)

Moreover,

    d=tr(cI_k-H)_+=sum_i(c-h_i)_+ <=sum_i(a_i-h_i)=L.       (11)

Let tau_s=sum_(i>k) f_s(a_i), and define

    L_s=sum_(i<=k) f_s(a_i)-tr f_s(H).

For a>=c and b>=0, the exact scalar identity

    |f_s(a)-f_s(b)|=s|a-b|/[(s+a)(s+b)] <= g|a-b|         (12)

holds. Since h_i<=a_i, it implies 0<=L_s<=gL.

By Lemma 2, (10)-(11), and the trace-positive-part identity,

    ||f_s(A)-f_s(C)||_*-tau_s
      = L_s+2tr(f_s(C)-f_s(A))_+
      <= gL+4g[tr(C-A)_++d]
      <= g(2eC+3L).                                       (13)

On range(P), B0>=cI_k and H>=0. The resolvent identity and the ideal property of the nuclear norm imply

    ||f_s(B0)-f_s(C)||_*
      = ||s(sI+B0)^(-1)(B0-C)(sI+C)^(-1)||_*
      <= gR.                                              (14)

Here the calculation is performed on range(P); both matrix-function differences vanish on its orthogonal complement. The factors have operator norms at most 1/(s+c) and 1/s, respectively. No commutation of B0 and C is used.

Combining (8)-(9) and (13)-(14),

    ||f_s(A)-f_s(B0)||_*-tau_s
      <= g(2eC+3L+R)
      <= g(2e0+3R+3L)
      <= 5g e0.                                           (15)

## 4. Arbitrary selected approximants

Return to B=Ahat_k and its prescribed projection P. Let b_1>=...>=b_k>=0 be its selected eigenvalues. In the same selected eigenvectors define B0 with eigenvalues a_1,...,a_k, and put

    r=sum_(i<=k)|a_i-b_i|=||B0-B||_*.

The eigenvalue perturbation inequality for Hermitian matrices in the nuclear norm gives

    r+tau <= ||A-B||_*,    hence r<=e(B).                   (16)

This is the standard inequality sum_i|lambda_i(X)-lambda_i(Y)|<=||X-Y||_* for ordered Hermitian eigenvalues; the remaining n-k eigenvalues of B are zero. Also,

    e0<=e(B)+r.                                            (17)

Because B0 and B use the same eigenvectors, (12) gives

    ||f_s(B0)-f_s(B)||_* <= gr.                            (18)

Equations (15)-(18) prove the absolute excess bound

    ||f_s(A)-f_s(B)||_*-tau_s
       <=5g[e(B)+r]+gr <=11g e(B).                        (19)

Each tail eigenvalue is at most c, so

    tau_s=sum_(i>k) a_i/(s+a_i) >=tau/(s+c)=g tau.         (20)

Thus, whenever e(B)<=epsilon tau,

    ||f_s(A)-f_s(B)||_* <= (1+11epsilon)tau_s.              (21)

In particular, (21) is uniform in s>0 and uses the actual selected eigenspaces.

## 5. Positive integral combinations and boundary cases

We use the standard positive integral representation of continuous nonnegative operator-monotone functions on [0,infinity):

    f(x)=alpha+beta x+integral_(0,infinity) x/(s+x) dnu(s), (22)

where alpha=f(0)>=0, beta>=0, nu is a positive measure and integral (1+s)^(-1) dnu(s)<infinity. One primary reference is P. Chansangiam, Integral Representations and Decompositions of Operator Monotone Functions on the Nonnegative Reals, arXiv:1304.7936v1, Proposition 1.1, p. 2. It represents f(x) as the integral of x(1+s)/(x+s) against a finite positive measure m on the compactified half-line [0,infinity]. Its endpoint atoms give alpha=m({0}) and beta=m({infinity}); on (0,infinity), set dnu(s)=(1+s)dm(s), which gives (22) and its stated integrability. Continuity at zero gives the stated extension there. The original target requires monotonicity for all real symmetric sizes; realification of complex Hermitian matrices gives the equivalent hypothesis for the usual representation theorem.

For fixed finite-dimensional A and B, (22) may be applied spectrally. The resulting matrix integrals converge absolutely: each positive matrix integrand has nuclear norm bounded by the finite sum of its scalar spectral values, whose integrals are finite. By the triangle inequality for the integral,

    ||f(A)-f(B)_P||_*
      <= alpha(n-k)+beta||A-B||_*
         +integral ||f_s(A)-f_s(B)||_* dnu(s).

The best-rank-k tail of f(A) is exactly

    tau_f=alpha(n-k)+beta tau+integral tau_s dnu(s).

If tau>0, apply (19)-(20), or equivalently (21), to every ridge atom. The linear term satisfies the original bound with constant one; the constant term contributes exactly alpha(n-k). Since epsilon>=0,

    ||f(A)-f(B)_P||_* <= (1+11epsilon)tau_f.

Finally, if tau=0, the hypothesis forces ||A-B||_*=0, so A=B and range(A) is contained in range(P). The selected functional-calculus truncation is f(B)_P=f(A)P, and

    f(A)-f(B)_P=f(0)(I-P).

Its nuclear norm is (n-k)f(0), exactly the best-rank-k tail of f(A). This handles all zero-tail, zero-matrix and rank-deficient cases without division by a vanishing quantity. As f(B)_P=f(Ahat)_k by the fixed selected eigenvectors, Theorem 1 follows. QED.

## References and scope

1. D. Persson, R. A. Meyer and C. Musco, Algorithm-agnostic low-rank approximation of operator monotone matrix functions, SIAM Journal on Matrix Analysis and Applications 46 (2025), 1-21; arXiv:2311.14023v2, Section 1.2 and the closing paragraph of Section 5. https://arxiv.org/html/2311.14023v2 . Their ordered result and counterexamples to constant one are credited; the present target is the unordered nuclear-norm question.
2. P. Chansangiam, Integral Representations and Decompositions of Operator Monotone Functions on the Nonnegative Reals, arXiv:1304.7936v1 (30 April 2013), Proposition 1.1, p. 2; Theorem 1.2 gives the equivalent weighted-harmonic-mean formulation. https://arxiv.org/pdf/1304.7936v1 .
3. The canonical RA-10 entry and Matthew J. Colbrook's independently reviewed commuting partial result are retained in the repository. That result proves the necessary lower bound C>=2. The present candidate claims only existence with C=11, not sharpness or a Frobenius/Schatten generalization.

The substantive new estimate is Lemma 2. The sharper isospectral ridge inequality and square inequality explored in earlier notes are not premises of this proof. No numerical search is used to establish the theorem.
