# MI-09 partial submission independent proof review

**Verdict: PASS for the expressly stated dimension-two result; PARTIAL for canonical MI-09.** No material gap found in the submitted theorem. It must not be presented as an all-parameter resolution of MI-09 or as a sharp constant for each individual unitarily invariant norm.

Reviewed 2026-09-11. Original: `.cache/colbrook-matrix-submission/nla_submission/proofs/MI-09-partial.tex`. SHA256 of the complete original decoded as UTF-8, replacing CRLF by LF, with no trimming: `bfd6c03510f22026783e87cee33e9cd81a46cb1710ed8aae46ec32a27009c6b0`.

## Exact target, established scope and remaining cases

The canonical `matrix-inequalities-and-norms/MI-09/README.md` asks for c_p^sym(m,n) for all m,n>=2 and all Schatten exponents 1<=p<=infinity. The submitted theorem establishes, for every m>=2,

\[
c_\infty^{\rm sym}(m,2)=\sqrt{6\sqrt3-9},
\]

and proves that this is also the smallest single constant valid simultaneously for every unitarily invariant norm on M_2. Its universal bound implies c_p^sym(m,2)<=sqrt(6sqrt(3)-9), but equality is established only at p=infinity. It further proves the sharp single-matrix numerical-radius inequality ||S(T)||_infinity<=sqrt(6sqrt(3)-9) w(T) for T in M_2.

The primary [Zhang paper](https://arxiv.org/html/2603.01046) was checked at §1.3, Problem 1.11, Problem 1.17 and Theorem 8.1. Problem 1.11 is the dimension-two universal unitarily invariant norm question within that context, whereas Problem 1.17 asks for individual Schatten constants. The source's established endpoints c_1^sym(m,n)=1 for all m,n>=2 and c_infinity^sym(m,n)=sqrt(2) for n>=3 are retained. The submission does not determine the remaining individual values for 1<p<infinity, n>=2, m>=2. No higher-dimensional finite-exponent case becomes exact merely by embedding the extremizer. This source comparison establishes scope; the new analytic proof is self-contained apart from standard elementary spectral/norm facts.

## Reduction and normal form

1. **Numerical-radius reduction:** the polar decomposition gives the mixed Schwarz inequality |v*Zv|<=sqrt((v*|Z|v)(v*|Z*|v)); scalar arithmetic-geometric mean then bounds this by v*S(Z)v. Summing absolute values and maximizing over unit v proves w(sum T_j)<=||sum S(T_j)||. The trace-norm triangle inequality gives tr S(sum T_j)<=tr sum S(T_j).

2. **All unitarily invariant norms:** S(T) and D=sum S(T_j) are positive. The operator-norm bound is the first partial-sum eigenvalue inequality. The trace bound implies the second partial-sum bound with the larger factor C=sqrt(6sqrt(3)-9)>1. Consequently lambda(S(T)) is weakly majorized by C lambda(D). Monotonicity of symmetric gauge norms under weak majorization supplies the stated inequality for every unitarily invariant norm. It does not make C sharp for every such norm; trace norm already has sharp constant one.

3. **Square-root formula:** for a nonzero positive 2-by-2 matrix P, Cayley–Hamilton verifies that (P+sqrt(det P)I)/sqrt(tr P+2sqrt(det P)) squares to P and is positive. Applying this to T*T and TT*, with their common trace and determinant, yields the submitted symmetric-modulus formula. The zero matrix is treated trivially; singular nonzero matrices have nonzero denominator and are included.

4. **Normal form:** phase multiplication and unitary similarity preserve both quantities in the radius inequality. With tr T=2h>0, diagonalizing S(T) makes the off-diagonal numerator 2h(t_12+conjugate(t_21)) vanish. Thus t_21=-conjugate(t_12), and a diagonal unitary makes t_12=b>=0. The real parts of the diagonal entries are h+x,h-x and their imaginary parts k,-k. Their ordering in S(T) forces x>=0. This gives precisely the displayed form, with no real-matrix restriction on T.

5. **Degenerate cases:** the argument may be proved on the dense set with nonzero trace, distinct S(T) eigenvalues and 0<h,x<q. Exceptional matrices are limits of such matrices; modulus, trace norm, operator norm and numerical radius are continuous. The proof explicitly uses this extension, so trace zero, repeated eigenvalues, h=0, x=0, h=q or x=q are not excluded from the theorem. T=0 is immediate. For clarity, the density can be seen by perturbing the Hermitian and skew-Hermitian parts: nonzero trace and nonscalar S are generic, and the endpoint equalities h=q or x=q can be broken by an arbitrarily small noncommuting perturbation.

6. **Scalar identities and constraints:** direct multiplication gives q^2=(h^2+x^2+k^2+b^2+|det T|)/2 and S(T)=diag(q+hx/q,q-hx/q). Eliminating |det T| gives (q^2-x^2)(q^2-h^2-b^2)=q^2 k^2. Here h<=q follows from the trace inequality. The expression for q^2 is the larger root of the corresponding quadratic; its value at x^2 is -x^2 k^2<=0, proving x<=q (including boundary cases by continuity). Scaling q to one gives exactly b^2=1-h^2-k^2/(1-x^2) and ||S(T)||=1+hx.

7. **Ellipse description:** the real and imaginary Hermitian parts have expectations h+xs and ks+bt, where (s,t) ranges over the unit disk, as follows from the Bloch-sphere parametrization of unit vectors in C^2 and projection onto two real coordinates. Thus the displayed ellipse, including collapsed ellipses, is the exact numerical range.

## Sharp numerical-radius estimate

8. **Quadratic maximization:** writing M as in the proof makes it positive semidefinite and gives w(T)^2=H+max_{||v||<=1}(v^T M v+2a^T v). A maximum can be taken on the unit circle. For lambda>lambda_max(M), completion of the square gives the upper bound H+lambda+a^T(lambda I-M)^(-1)a. Equality holds when the displayed inverse times a has norm one. If it never reaches one, a is orthogonal to the top eigenspace and the inverse has a finite endpoint limit of norm at most one; adding a top eigenvector component to reach norm one realizes equality in the limit. Thus the infimum identity is exact, including the hard boundary case. No unjustified min-max interchange is used.

9. **Region g>=hx:** on the generic set this gives g>0, P=1-X>0, Q=1-H>X. Substituting b^2=Q-z/P verifies det(QI-M)=-HXz/P<=0, so lambda_max(M)>=Q. Every admissible lambda can therefore be written Q+d with d>0. Direct expansion gives Delta=d(g+d)+zX(d-H)/P>0 and f=1+d+HX(d+z/P)/Delta.

10. **Polynomial identity:** independently expanding g Delta(f-1-HX/g) gives its z-free part d^2(g^2-HX+gd). The coefficient of zX/P is (gd-HX)(d-H)+gH, which reduces to gd^2-HQd+HQP because g+X=Q and HX+g=QP. This reproduces the exact key identity without numerical sampling.

11. **Signs:** g>=hx implies g^2>=HX. The further identity gP-HQ=g^2-HX proves HQ<=gP. For 0<=d<=P, gd^2+HQ(P-d)>=0; for d>=P, d(gd-HQ)+HQP>=0. Thus both terms in the identity are nonnegative, and division by g Delta is legitimate. Taking the infimum proves w(T)^2>=1+HX/g.

12. **Optimization in this region:** with p=hx, H+X>=2p and g>=p imply p<=1/3 and g<=1-2p. The function g/(g+p^2) is increasing in g, giving the displayed rational upper bound F(p)=(1+p)^2(1-2p)/(1-p)^2. Its derivative has the sign of p^2-4p+1 on [0,1/3]; the unique critical point there is p=2-sqrt(3). Direct substitution gives F(p)=6sqrt(3)-9. Boundary values do not exceed it.

13. **Region g<=hx:** w(T)>=lambda_max(Re T)=h+x. If p<=1/3, the region condition gives (h+x)^2>=1+p and hence ratio squared <=1+p<=4/3. If p>=1/3, AM–GM gives (h+x)^2>=4p and (1+p)^2/(4p)<=4/3 for 1/3<=p<=1. Finally 4/3<6sqrt(3)-9, e.g. by the exact positive comparison 18sqrt(3)>31 (972>961 after squaring). This covers all generic matrices and continuity covers the remainder.

## Exact attainment

At p=2-sqrt(3), 0<p<1/3, all square roots in h,b,w,z are real and their denominators positive. The identities b^2+z^2=w^2 and bz=wh follow directly from their definitions. Expanding each 2-by-2 determinant therefore gives zero. Their squared Frobenius norms simplify to (w+h)^2 and (w-h)^2 respectively. Since w>h, both are nonzero rank-one matrices, and these positive numbers are exactly their nonzero singular values.

For a rank-one real matrix T, the established modulus formula simplifies to (T^T T+TT^T)/(2||T||_1). Applying it to the two summands gives the displayed diagonal symmetric moduli; their diagonal differences are respectively h and -h, and their traces w+h and w-h. Their sum is exactly wI.

The sum of the two matrices is [[2h,b],[-b,0]]. Its trace norm is two: its squared Frobenius norm is 2+2p and |det|=1-p. The same modulus formula then gives diag(1+p,1-p). Consequently the ratio in operator norm is exactly (1+p)/w, whose square is 6sqrt(3)-9. Zero padding preserves it for every m>=2. The single-matrix radius bound is sharp as well: the already established bound combined with w(T_1+T_2)<=w and ||S(T_1+T_2)||=Cw forces w(T_1+T_2)=w. Alternatively, maximizing its k=0 ellipse gives that value directly.

## Limitations and disposition

No numerical tests are used as proof evidence; the optimization, sign certificate and rank-one equalities above are algebraic. No material correction to the original theorem is needed. The continuity and trust-region boundary explanations are concise in the submission but valid; this review expands their justifications. The canonical entry must remain **Partially resolved**, with the new exact n=2 operator endpoint and the sharp common UI-norm constant stated explicitly. All individual finite exponents 1<p<infinity remain undetermined by this submission. This review is not formal verification, exhaustive novelty certification or external peer review. Original proof and canonical files were not edited by this reviewer.
