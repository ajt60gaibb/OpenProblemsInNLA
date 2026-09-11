# Sharp factor-two excess transfer for commuting PSD matrices

This is a partial result for Schatten norms other than Frobenius, not a resolution of the noncommuting operator-monotone nuclear question.

Let f be continuous, nonnegative, nondecreasing, f(x)/x nonincreasing. Let A,B have a common orthonormal eigenbasis, and let S be a specified set of exactly k basis vectors supporting B (padding zero b_i). Define C with entries f(b_i) on S and zero elsewhere. For any 1<=p<infinity, tau=a_(k+1)>0, c=f(tau)/tau,

||f(A)-C||_p^p - sum_(i>k)f(a_i)^p
<= 2 c^p (||A-B||_p^p - sum_(i>k)a_i^p).

Consequently p-th-power relative excess and norm-relative excess both grow by at most2; both constants are optimal, even for operator-monotone powers. For p=2 this follows from the stronger noncommuting result already proved, but this argument treats every finite p.

Proof. Write delta_A = L_A + R_A, where
L_A=sum_(i<=k)a_i^p - sum_(i in S)a_i^p,
R_A=sum_(i in S)|a_i-b_i|^p.
Use analogous L_f,R_f. Match selected indices below the top k to omitted top indices. Since f(y)<=cy above tau and f(x)>=cx below tau, L_f<=c^p L_A. Also L_A>=sum_(i in S)(tau^p-a_i^p)_+.

Scalar bound for all a,b>=0:
|f(a)-f(b)|^p <=c^p[|a-b|^p+(tau^p-a^p)_+].
If max(a,b)>=tau, the pairwise c-Lipschitz bound suffices. If a>=b and a<=tau, then f(a)-f(b)<=f(tau)(1-b/a), and
 tau^p(1-b/a)^p <= (a-b)^p + tau^p-a^p,
since (1-b/a)^p<=1. If b>=a and b<=tau, use f(b)-f(a)<=f(tau)(1-a/b), and
 (tau^p-b^p)(1-a/b)^p<=tau^p-a^p.
Zero endpoints follow directly or by continuity. Summing gives R_f<=c^p(R_A+L_A), hence delta_f<=c^p(R_A+2L_A)<=2c^p delta_A.

Since c^p T_A<=T_f, relative excess transfers. For norm notation, convexity gives (1+2eps)^p>=2(1+eps)^p-1. Sharpness uses A=I_(N+1) directsum0, k1, B=b in the null coordinate, f=x^r: excess ratio (1+b^(pr))/(1+b^p)->2; then N->infinity gives norm-relative sharpness.
