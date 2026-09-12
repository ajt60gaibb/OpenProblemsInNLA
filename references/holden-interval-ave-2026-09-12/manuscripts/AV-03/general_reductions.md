# General reductions and a second scalar-shooting subclass

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation.

These results do not solve unrestricted AV-03. They retain the rational binary-input, exact-output, deterministic bit-complexity model.

## 1. Residual accuracy sufficient for exact recovery

Use q,h,D from `result.md`, and put

    G = q n! h^(n-1).

For every d in [-1,1]^n,

    ||(A-diag(d))^-1||_infinity <= G.

To prove this, the determinant of q(A-diag(d)) is multi-affine in d. At each vertex of the cube it is a nonzero integer. All vertex determinants have the same sign, since the family is regular and the cube is connected. Multi-affine interpolation expresses the determinant at any d as a convex combination of the vertex values. Its absolute value is therefore at least 1. Every cofactor has absolute value at most (n-1)!h^(n-1). The adjugate formula and summing n entries in a row give the stated bound after multiplying by q.

For f(x)=Ax-|x|, secant slopes of the absolute value give

    f(x)-f(y)=(A-diag(d))(x-y),   d in [-1,1]^n.

Thus

    ||x-y||_infinity <= G ||f(x)-f(y)||_infinity.

If an algorithm finds a rational x_hat with residual at most 1/(4DG), then ||x_hat-x*||_infinity<=1/(4D). Selecting the signs of x_hat and solving the resulting linear system gives the exact x*, including when some x*_i=0. The logarithm of the required inverse residual tolerance is polynomial in the input length.

This is a reduction, not the missing approximation algorithm. A method whose number of iterations depends polynomially on G rather than on log G need not be polynomial-time in the required model.

## 2. Exact equivalence with P-matrix LCP, with the exceptional Cayley case handled

A P-matrix has every principal minor positive. The LCP(M,q0) asks for v>=0 and u=Mv+q0>=0 with u_i v_i=0 for every i.

From a regular AVE, A-I is nonsingular. Put

    M=(A-I)^-1(A+I),       q0=(A-I)^-1 b.

Writing x=u-v with u=(|x|+x)/2, v=(|x|-x)/2 gives exactly this LCP. For D=diag(d),

    A-D=(A-I)[(I+D)/2 + M(I-D)/2].

At a vertex d, the bracket has either the identity column or the corresponding M column in each position. Its determinant is the principal minor of M on the positions where d_i=-1. Since all det(A-D) have the same sign as det(A-I), every such principal minor is positive.

Conversely, start from a rational P-matrix M0 and rational q0. Choose an integer rho from {1,...,n+1} with det(rho M0-I)!=0. Such a choice exists because det(z M0-I) is a nonzero polynomial of degree n, having at most n distinct roots. Test the candidates with exact determinants. Scaling the LCP equations by rho gives an equivalent LCP with M=rho M0, q=rho q0, u'=rho u and unchanged v. The matrix M remains P.

Define

    A=(M+I)(M-I)^-1,       b=2(M-I)^-1 q.

Then A-I=2(M-I)^-1. The displayed factorization above applies. Every determinant of its bracket is a convex combination of the positive principal minors of M, hence positive on the entire diagonal cube. This proves the regularity promise, and x=u'-v gives the AVE solution. Recover v=(|x|-x)/2 and u=u'/rho.

All rational matrix operations and the n+1 determinant tests have polynomial bit complexity by standard minor bounds. This avoids silently assuming that M0-I is nonsingular. It also shows why obtaining an unrestricted polynomial solver is the actual target, rather than merely obtaining polynomial output bit length.

The repository and its cited 2026 survey already state the general AVE/P-LCP connection. The proof here is included for auditing transformations and the scaling exception, not claimed as a new equivalence theorem.

## 3. A second polynomial subclass: one feedback variable and a triangular subsystem

**Theorem F.** In addition to the regularity promise, suppose the leading (n-1) by (n-1) block of A is lower triangular and |a_ii|>1 for i<n. The last row and last column can be arbitrary. There is an exact deterministic polynomial-bit AVE algorithm on this class.

This class is not restricted to lower Hessenberg matrices. In particular it includes dense arrows and triangular systems with one feedback variable.

### Proof

Set x_n=t. For i=1,...,n-1, successively form

    c_i(t)=b_i-a_in t-sum_(j<i) a_ij x_j(t)

and solve a_ii x_i-|x_i|=c_i(t). For |a|>1, the scalar map z->az-|z| is a continuous strictly monotone bijection. Its inverse is continuous piecewise affine and globally 1/(|a|-1)-Lipschitz. Explicitly, for c!=0, set s=sign(a)sign(c) and z=c/(a-s); for c=0 set z=0.

These formulas give a continuous, finite piecewise-affine parametrization satisfying the first n-1 equations. Define the last residual g(t) as before. If g(t)=g(u), the same coordinatewise secant argument gives (A-diag(d))(x(t)-x(u))=0. Since x_n(t)-x_n(u)=t-u, regularity implies t=u. Therefore g is strictly monotone. The promised root lies in [-D,D] in its t coordinate.

Choose an integer C at least 2, every |a_ij|, and every 1/(|a_ii|-1) for i<n, and put B0=(n+1)C^2, K=B0^(n-1). Induction in the displayed recursion gives

    |x_i(t)-x_i(u)| <= B0^i |t-u|   (i<n),
    |x_n(t)-x_n(u)| = |t-u|.

Indeed its i-th Lipschitz bound is at most C^2(1+sum_(j<i) B0^j), which is at most B0^i. Bisection to width 1/(2DK), followed by the selected exact linear solve, consequently works just as in Theorem H.

For bit complexity, clear denominators with q. At each scalar inversion the integer divisor is q a_ii-q s_i, of magnitude at most h and nonzero. At a fixed dyadic t the denominator of every intermediate coordinate divides the dyadic denominator times the product of these at most n-1 integer divisors. The magnitude and numerator bounds follow by the same finite recursion. Thus each evaluation and the polynomially many bisections have polynomial bit complexity. No lower bound on |a_ii|-1 independent of coefficient bit length is assumed. This proves Theorem F.

### Non-Hessenberg regular examples

Let T be lower triangular of order n-1 with diagonal entries 2 and nonpositive entries below the diagonal. Set

    A = [[T, 2*1], [2*1^T, 0]],       n>=2.

For every d, T-diag(d_1,...,d_(n-1)) has a nonnegative inverse: solve by forward substitution, or expand its strictly lower triangular nonnegative part in a finite Neumann series. Its inverse diagonal entries are at least 1/3. The scalar Schur complement of this block in A-diag(d) is

    -d_n - 4*1^T (T-diag(d_1,...,d_(n-1)))^-1 1
      <= 1 - 4(n-1)/3 < 0.

The leading block and Schur complement are nonsingular, proving regularity. With T diagonal, this is an arrow with nonzero coupling to every leaf; for n>=4 it is not simultaneously permutation-similar to a Hessenberg matrix. To see this, in any ordering every edge must join consecutive positions to be compatible with a symmetric Hessenberg zero pattern, but the center of a star with at least three leaves cannot be consecutive to all its neighbors. Theorem F nevertheless applies.

`feedback_solver.py` implements this result; `test_feedback.py` contains exact tests.

## 4. A nonstationarity observation, not a complexity result

For psi(x)=||Ax-|x|-b||_2^2/2, the gradient on a strict orthant is (A-diag(s))^T r, where r=Ax-|x|-b. At a point on coordinate hyperplanes, every convex combination of limiting gradients has the form (A-diag(d))^T r with d in [-1,1]^n. Under the promise it cannot vanish unless r=0. This shows that the convex hull of limiting branch gradients contains zero only at the root.

It does not prove that a generic descent method reaches the root in polynomial bit complexity. Quantitative bounds obtained from the inverse estimate involve G in value, which may be exponential in the input length; region-by-region paths can also be exponentially long. This approach was not promoted to a full algorithm.
