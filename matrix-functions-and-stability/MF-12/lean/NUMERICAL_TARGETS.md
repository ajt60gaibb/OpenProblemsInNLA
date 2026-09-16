# MF-12 numerical and general statement boundary

This is a proof-free draft for independent review and Linux elaboration.
Original mathematics: Matthew J. Colbrook, Department of Applied Mathematics
and Theoretical Physics, University of Cambridge. Formalization: George
Stepaniants, Department of Computing and Mathematical Sciences, California
Institute of Technology, Pasadena, California, USA. No contact email is added.

## Complete canonical target and meaning

For every real gamma >= 0, construct a fixed positive dimension d and a finite
family M of exactly two distinct real d-by-d matrices. There must be fixed real
constants 0 < c <= C such that c*n^gamma <= g_M(n) <= C*n^gamma for every
integer n >= 1. In addition the actual sequence g_M(n)^(1/n) must converge to
1, giving joint spectral radius one in the canonical definition. Neither the
matrices, dimension, nor constants may depend on n. Comparability is required;
convergence of g_M(n)/n^gamma is not asserted.

Every product is the reverse product of a chronological list, so the last
chosen matrix multiplies on the left. `wordNorms M n` includes all actual lists
of length n with every factor in M; `familyGrowth` is the real supremum of
this set. An exported finite-maximum theorem must prove the set is nonempty,
finite, its supremum is attained by an actual list, and every allowed list is
bounded above by it. Pair-to-binary-word equality is a separate exported bridge,
not an assumption of injective coding or a restriction of switching words.
The empty product is the genuine matrix identity. The final norm is always
the induced Euclidean operator norm via Mathlib's continuous linear map over
R. Entry maxima are genuine finite entry suprema, with attained-maximum and
norm-comparison theorems; they are auxiliary only.

## Fixed fractional family, 0 < alpha < 1

Use lambda = 1/4 and mu = lambda^(1-alpha), with real powers. Establish
0 < lambda < mu < 1. Write J_t = [[t,t],[0,t]],
A_alpha = diag(1,J_lambda,J_mu,1), and use the exact rectangular arrays

V = [[1,0],[0,0],[1,0],[0,0],[0,1],[0,1]],
U = [[1,-1,0,1,0,0],[0,0,0,0,0,1]].

P = V*U is fixed and has a negative entry. Prove U*V = I_2, P^2 = P and
A_alpha != P. No positivity or common invariant-cone hypothesis is introduced.
For every natural q >= 0, prove the actual Jordan power identity and
U*A_alpha^q*V = [[1-loss(q),gain(alpha,q)],[0,1]],
where loss(q)=(q:R)*lambda^q and gain(alpha,q)=(q:R)*mu^q use natural powers.
For q >= 1, 0 < loss(q) <= 1/4. Include q=0 with both scalars zero. The exact
real-power identity is gain(alpha,q)=q^alpha*loss(q)^(1-alpha) for every q.

For every finite list qs of nonnegative gaps, including the empty list and
zero gaps, define w_i=product of (1-loss(q_j)) for j>i. Prove 0<=w_i<=1,
0<=a=product(1-loss(q_j))<=1, and the exact telescoping identity
sum_i loss(q_i)*w_i=1-a. Prove the actual compressed product equals
[[a,z],[0,1]], with z=sum_i gain(alpha,q_i)*w_i and
0<=z<=(sum qs)^alpha. This is a finite Holder estimate on the entire list.
A finite sample or a selected reset pattern cannot discharge this obligation.

Encode every binary chronological word as gaps of A separated by P. Prove
all word lengths, exact matrix products and the reset factorization, including
no reset and a single reset. The fixed A powers have every entry bounded in
absolute value by H=(1-mu)^(-1). A deliberately loose bound

C_alpha = 1728 * H^2

then controls the genuine operator norm of every positive-length binary word
by C_alpha*n^alpha. One exact route bounds each entry of
A^r V B U A^s by 144*H^2*maxEntry(B), bounds the norm of a 6-by-6 matrix by
six times its entry maximum, and uses maxEntry(B)<=1+n^alpha<=2*n^alpha.
This avoids rectangular singular-value calculations; the complete norm and
all switching words are retained. The source's sharper 2*sqrt(6)*H^2 is not
claimed.

## A lower bound at every length

For every n >= 4 set q=Nat.log 4 n, k=n/(q+1), r=n-k*(q+1), with natural
integer division. Require q>=1, k>=1, 4^q<=n<4^(q+1),
4^q>=2*(q+1), r+k*(q+1)=n and k*loss(q)>=1/4 over R.
The exact chronological word is k repetitions of q copies of A then P,
followed by r copies of A. Thus its actual product is A^r*(P*A^q)^k and its
length is exactly n. For n<4, use n copies of A instead.

Use the exact Bernoulli estimate (1-ell)^k <= 1/(1+k*ell) for
0<=ell<1 and every natural k. When k*ell>=1/4 this gives
1-(1-ell)^k>=1/5. In the compressed geometric-series entry,
gain/loss=(4^q)^alpha >= (n/4)^alpha. Applying the actual six-dimensional
product to V*e_2, whose Euclidean norm is <=2, yields the explicit constant

c_alpha = lambda^alpha/10.

The exported lower bound concerns the prescribed actual word at every n>=1,
with small lengths proved using ||A^n||_2>=1 and c_alpha*n^alpha<=1.
It is not a subsequence statement. Consequently 0<c_alpha<=C_alpha and
c_alpha*n^alpha<=g_{A_alpha,P}(n)<=C_alpha*n^alpha at every positive n.
The replacement of the source's exponential constant by 1/10 is explicit and
uses no interval computation.

## Actual root limit and every real exponent

Prove the general squeeze theorem: for every gamma>=0, c,C>0 and real
sequence g with c*n^gamma<=g(n)<=C*n^gamma for all n>=1, the actual real-power
sequence g(n)^(1/(n:R)) tends to 1 atTop. The value at n=0 is irrelevant to
this limit. No default-valued limit or unproved JSR assignment is allowed.

For every natural m define J_m=I+N of order m+1, with N the first upper
shift. Prove every actual entry of J_m^n equals choose(n,s-r) when r<=s and
zero otherwise. Let L_0=1, and L_m=1/(m^m) for m>=1, with natural powers.
For all n>=1 prove L_m*n^m<=||J_m^n||_2<=(m+1)*n^m, with the case n<m and
m=0 included. The pair {J_m,0} is distinct and has exactly that same growth.

For all d,e>=1, reindex the actual Kronecker product through
Fin d x Fin e equiv Fin(d*e). Establish the exact identity of every binary
word product with the base word product tensored with J_m^n. Prove the generic
norm comparison

||B||_2*||D||_2/(d*e) <= ||B tensor D||_2
  <= (d*e)*||B||_2*||D||_2.

This follows from entryMax<=||.||_2<=dimension*entryMax and multiplicativity
of the genuine entry maximum. It intentionally avoids a new spectral-norm
Kronecker/SVD theorem; the final norms remain genuine Euclidean operator norms.
The lifted pair must remain distinct. With e=m+1, the explicit bounds
c_alpha*L_m/(6*e) and (6*e)*C_alpha*e suffice for exponent alpha+m.
The integer case uses {J_m,0}. For noninteger gamma take m=floor(gamma) and
alpha=gamma-m in (0,1), then combine these exact fixed-dimensional results.
The final declaration must exhibit a two-element finite real family, constants
0<c<=C, every-length comparability and actual root convergence for every real
gamma>=0.

## Deliberate scope and gates

No dyadic-rational-entry realization, specific irrational example, density of
rational-entry exponents, sharp constants or optimal dimension is claimed.
Those strengthen the retained canonical question and are not needed for it.
No outside mathematical theorem from the source article is assumed without a
Mathlib theorem or proof in this project.

All proposed Challenge declarations are deliberate placeholders only. Before
proof bodies: two independent statement approvals, actual remote non-root
Linux elaboration, and immutable source freeze. After implementation: all
LeanCert kernel assertions, transitive standard-axiom audit, real Comparator
with no definition holes, default-kernel replay and negative controls, and two
independent final referees applying scoped Tau Ceti requirements. No local
Lean/Lake/build or cache download is authorized; no verified count increment is
claimed by this statement package.
