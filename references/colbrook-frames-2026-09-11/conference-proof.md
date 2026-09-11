# Rational contraction certificates for redundancy-two complex ETFs

**Submitted construction and certificates: Matthew J. Colbrook**  
Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom. Email: m.colbrook@damtp.cam.ac.uk.

This exposition was written during the independent review on 2026-09-11 to explain the mathematical claim encoded by the user-supplied conference certificates and programs. No conference manuscript accompanied those files. This is reviewer-authored exposition, not an attributed original manuscript or a claim of discovery priority. Certificate identity and execution evidence are recorded in [the independent review](verification/reviews/FR-09-review.md).

The supplied, verified certificates establish existence of a unit-norm complex equiangular tight frame with 2d vectors in dimension d for d=166,209,256,1505. The corresponding Hermitian conference orders are 332,418,512,3010. They do not prove the all-dimension conjecture FR-09, nor certify every dimension in the supplied report range 166–256.

## 1. Exact model

Fix d>=3 and h=floor((d-1)/2). Let a,b be complex sequences indexed modulo d with

\[
a_0=0,\quad a_{d-j}=\overline{a_j},\quad |a_j|=1\ (j\ne0),
\qquad b_0=1,\quad |b_j|=1.
\]

When d is even the certificates fix a_{d/2}=1. There are h+d-1 independently parameterized unit phases. A certificate supplies integers p_v and a positive common denominator D defining exact anchors

\[
z_v=\frac{D^2-p_v^2+2ip_vD}{D^2+p_v^2},\qquad |z_v|=1.
\]

It selects n=d-1 distinct phases. Replace each selected phase by z_v q(t_k), where t is real and

\[
q(t)=\frac{1+it}{1-it}.
\]

The paired a entries are replaced by conjugates, and unselected phases remain at their anchors. This preserves every modulus and symmetry condition exactly for all real t.

Define the cyclic correlation sums

\[
R_s(t)=\sum_{j=0}^{d-1}
\left(a_j(t)\overline{a_{j+s}(t)}+b_j(t)\overline{b_{j+s}(t)}\right).
\]

Let F(t) in R^n consist of the real and imaginary parts of R_s for 1<=s<d/2, followed by the real part of R_{d/2} when d is even. This has exactly n components. Since R_{d-s}=conjugate(R_s) and the half-period correlation is real, F=0 is equivalent to every nonzero correlation vanishing. Also R_0=2d-1 identically.

## 2. Contraction theorem and explicit nonlinear bounds

Write J=DF(0). A certificate supplies an exact rational n by n matrix M and a positive rational radius r. Suppose certified upper bounds satisfy

\[
\|MF(0)\|_\infty\le a,\qquad
\|I-MJ\|_\infty\le b,\qquad
\|M\|_\infty=K,
\]

and

\[
b<1,\qquad a+br+16dKr^2<r,\qquad b+32dKr<1.\tag{1}
\]

Then F has a zero in the closed box ||t||_infinity<=r.

To prove the constants, for every real t,

\[
|q(t)|=1,\qquad |q'(t)|=\frac{2}{1+t^2}\le2,
\qquad |q''(t)|=\frac{4}{(1+t^2)^{3/2}}\le4.
\]

Conjugated phases obey the same bounds. Each summand in a correlation is a product of two factors, each depending on at most one coordinate. If those coordinates differ, the sum of the absolute values of all Hessian entries is at most 4+4+2(2)(2)=16. If they coincide, the one second derivative is bounded by the same product-rule sum 16. Fixed factors or zero a entries only reduce the bound. Taking real or imaginary parts cannot increase it. There are 2d summands, so for each real component F_i,

\[
\sum_{k,l}|\partial_k\partial_l F_i(t)|\le32d
\quad\text{for every real }t.
\]

Consequently

\[
\|DF(t)-J\|_\infty\le32d\|t\|_\infty,
\qquad
\|F(t)-F(0)-Jt\|_\infty\le16d\|t\|_\infty^2.
\]

Set T(t)=t-MF(t). On the closed radius-r box its norm is at most a+br+16dKr squared, and its Lipschitz constant is at most b+32dKr. Conditions (1) therefore make T a self-map and a strict contraction. Banach's fixed-point theorem gives a unique fixed point in this selected-coordinate box. Since ||I-MJ||<1, MJ is invertible; as both factors are square, M is invertible. The fixed-point equation MF(t)=0 thus implies F(t)=0. The uniqueness assertion concerns the fixed unselected anchors and this box, not all frames or equivalence classes.

## 3. What the integer verifier proves

The verifier encloses the exact anchors, F(0), and J on a fixed grid S=2^160. Interval endpoints are unbounded Python integers representing endpoint/S; every division rounds downward at the lower endpoint and upward at the upper endpoint. The derivative of an anchor z q(t) at zero is 2iz; conjugate a partners have the conjugate derivative. Direct differentiation of R_s yields the Jacobian used by the program.

Let M=N/D_M with an integer matrix N. Matrix actions on intervals use sign-aware exact integer sums and outward division. This supplies a. K is computed exactly as max_i sum_j |N_ij|/D_M. All pass/fail comparisons use rational arithmetic; decimal outputs are displays only.

The optional fast Jacobian product uses an integer matrix C and S_J=2^20 with a rigorously computed entrywise bound |J_ij-C_ij/S_J|<=epsilon. Hence

\[
\|I-MJ\|_\infty
\le \frac{\max_i\sum_j|(D_M S_J)\delta_{ij}-(NC)_{ij}|}{D_M S_J}
  +Kn\epsilon.\tag{2}
\]

The program checks that every entry fits signed int64 and that

\[
\left(\max_i\sum_k|N_{ik}|\right)\max_{kj}|C_{kj}|+D_MS_J<2^{63}.
\]

This bounds each product and every possible partial sum in the integer matrix multiplication by a value below the signed limit. The product is therefore exact; subsequent row sums use unbounded integers. The final Kn epsilon term accounts for the entire coarse-grid Jacobian error. Alternatively, the pure-Python path computes all matrix products by integer interval arithmetic without int64.

Each of the four supplied certificates uses r=10^-8, D=2^60, D_M=2^32, S=2^160, and S_J=2^20. Full rational bounds and exact inequality outcomes are retained in the verification records. Neither the floating-point root search nor its displayed residual is needed for the theorem once a certificate passes.

## 4. From a zero to a conference matrix and a frame

Use the convention A_{ij}=a_{j-i}, B_{ij}=b_{j-i}. Then A is Hermitian, and A,B are commuting normal circulant matrices. The off-diagonal entries of AA*+BB* are the correlation sums (up to reversal of the shift). Thus F(t)=0 gives

\[
A^2+BB^*=(2d-1)I_d.
\]

Define

\[
H=\begin{pmatrix}A&B\\B^*&-A\end{pmatrix}.
\]

This matrix is Hermitian with zero diagonal and unimodular off-diagonal entries. Commutativity and normality give

\[
H^2=\begin{pmatrix}A^2+BB^*&AB-BA\\B^*A-AB^*&B^*B+A^2\end{pmatrix}
=(2d-1)I_{2d}.
\]

Since trace H=0, its eigenvalues plus and minus sqrt(2d-1) each have multiplicity d. Therefore

\[
G=I_{2d}+\frac{H}{\sqrt{2d-1}}
\]

is positive semidefinite of rank d, with eigenvalues 2 and 0, diagonal one, and off-diagonal squared modulus 1/(2d-1). If U has orthonormal columns spanning its positive eigenspace, V=sqrt(2) U* satisfies V*V=G and VV*=2I_d. Its 2d columns have unit norms and the exact canonical FR-09 inner products.

The frame can moreover be chosen two-circulant. Apply the unitary d-point Fourier transform to each block of G. Reordering the coordinates gives d positive semidefinite 2 by 2 matrices G_k. Each satisfies G_k squared=2G_k and has trace two, because G_11+G_22=2I. Hence each is rank one with eigenvalues 2,0. Factor G_k as [x_k,y_k]*[x_k,y_k]. Inverse Fourier transform of the two diagonal matrices with diagonals x_k,y_k yields circulant matrices X,Y such that [X Y]*[X Y]=G. This proves two-circulant synthesis without requiring any additional invertibility of B or a diagonal Gram block.

The relevant established characterization is [Iverson, Jasper, and Mixon, *More on the optimal arrangement of 2d lines in C^d*, arXiv:2410.17379v1, Theorem 23 and equation (5)](https://arxiv.org/html/2410.17379v1#S4). The general signature-to-ETF criterion is also stated in [Glazyrin, arXiv:2608.16116v1, Proposition 1](https://arxiv.org/html/2608.16116v1#S1). Both primary sources were accessed on 2026-09-11. The direct derivation above specifies all hypotheses actually used here.

## 5. Exact scope

This is an existence proof supported by finite rational certificates. It need not give rational frame entries, a closed-form phase solution, a classification, or a proof that such a certificate exists in every dimension. Only four dimension-specific certificates accompany this submission. The catalog's remaining reports are not substitutes for their missing anchors and preconditioners. FR-09 therefore remains partially resolved.
