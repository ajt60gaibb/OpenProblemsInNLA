# MI-15: exact SOS certificates in orders 8 through 12

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation.

**Date:** 12 September 2026. [Submission, verified affiliation and independent review](../README.md).

**Classification: NEW PARTIAL RESULT.** Complete exact finite-order proof candidates are supplied for n in {8,9,10,11,12}. This classification is relative to the unresolved scope recorded in the canonical README; historical novelty beyond that source has not been established. The universal assertion for every n remains unresolved here.

## Exact statement addressed

For n in {8,9,10,11,12}, let x_{-(n-1)},...,x_{n-1} and y_{-(n-1)},...,y_{n-1} be independent real variables, and set X_{ij}=x_{i-j}, Y_{ij}=y_{i-j} for 1<=i,j<=n. Then

```math
F_n=2\|X\|_F^2\|Y\|_F^2
-2(\mathop{\mathrm{tr}}\nolimits X^TY)^2-\|XY-YX\|_F^2
\tag{1}
```

is a sum of at most 2(n-1)^2 squares of homogeneous quadratic real polynomials. All the variables and coefficients in (1) are exactly those in the repository statement; there is no symmetry, bandwidth, positivity, or genericity restriction on X,Y.

The supplied certificates use rational Gram matrices. The real coefficients allowed in the problem are sufficient for the associated square-root factors; rational coefficients for the individual squares are not asserted or required.

## 1. Wedge-coordinate identity

Let I={-(n-1),...,n-1}, w_a=n-|a|, and

```math
z_{ab}=x_a y_b-x_b y_a\quad(a< b).
```

Since ||X||_F^2=sum w_a x_a^2 and tr(X^TY)=sum w_a x_a y_a, direct expansion gives

```math
2\|X\|_F^2\|Y\|_F^2-2(\mathop{\mathrm{tr}}\nolimits X^TY)^2
=2\sum_{a< b}w_aw_bz_{ab}^2.
\tag{2}
```

The commutator is linear in these wedges:

```math
(XY-YX)_{ij}=\sum_{k=1}^n
(x_{i-k}y_{k-j}-x_{k-j}y_{i-k}).
\tag{3}
```

Wedges involving the central index 0 cancel in (3), because their corresponding Toeplitz basis matrix is I_n. They therefore contribute the explicit nonnegative squares

```math
2n\sum_{a\ne0}(n-|a|)(x_0y_a-x_ay_0)^2
\tag{4}
```

to F_n, without any commutator term.

Order the pairs a<b of nonzero indices lexicographically, and let z be that wedge vector. Its dimension is d=binom(2n-2,2). Let C be the integer coefficient matrix of (3) in this vector, and put

```math
Q_0=2\mathop{\mathrm{diag}}\nolimits_{a< b}(w_aw_b)-C^TC.
\tag{5}
```

Then F_n equals (4)+z^TQ_0z. The exact verifier independently expands (1), rather than assuming (2)-(5), and compares all quartic coefficients with the certificate expression.

## 2. Gram corrections that preserve the polynomial

For every ordered quadruple a<b<c<d of nonzero indices,

```math
z_{ab}z_{cd}-z_{ac}z_{bd}+z_{ad}z_{bc}=0.
\tag{6}
```

This identity follows by expanding the six products of coordinates and canceling them. For a real parameter t, adding the symmetric matrix entries

- +t in positions ((a,b),(c,d)) and its transpose;
- -t in positions ((a,c),(b,d)) and its transpose;
- +t in positions ((a,d),(b,c)) and its transpose

changes z^TQz by twice t times (6), hence does not change the polynomial.

The file `certificates/nN.json` lists all nonzero corrections for its order. An entry `[a,b,c,d,t_num]` means t=t_num/D, where `gram_denominator` gives the positive integer D. Unlisted quadruples have t=0. Thus the file unambiguously defines a rational symmetric Q with

```math
F_n=(4)+z^TQz.
\tag{7}
```

For all five certificates D=1,000,000. No rounded matrix is accepted merely because it is close to a feasible matrix: identities and positivity are verified again after rationalization.

## 3. Exact nullspace and rational complement

For k=0,...,n-2 define a vector u_k in R^d which is 1 on pairs satisfying

```math
b-a=2(n-1)-k
\tag{8}
```

and 0 elsewhere. Their supports are nonempty and disjoint. The checker verifies, by integer arithmetic, that

```math
Q u_k=0\quad(k=0,\ldots,n-2).
\tag{9}
```

These identities are claims about the supplied matrices, not an unproved all-order necessity theorem.

Construct a rational basis matrix B for their orthogonal complement as follows. Within each support group choose its first index r and use e_i-e_r for every other index i in that group. On indices outside all groups use the standard vectors e_i. The columns of B and the vectors u_k together span R^d, with each u_k orthogonal to every column of B. Hence B has

```math
h=d-(n-1)=2(n-1)(n-2)
```

columns. By (9), positivity of Q is equivalent to positivity of G=B^TQB.

## 4. Exact positive-definiteness certificate

Let Q_num=DQ and G_num=B^T Q_num B. These are integer matrices. The JSON file supplies an h-by-h integer matrix T_num, together with a positive scaling denominator E=1,000,000,000. The checker computes the integer matrix

```math
H_{\rm num}=T_{\rm num}^T G_{\rm num}T_{\rm num}
\tag{10}
```

and verifies symmetry and, in every row,

```math
(H_{\rm num})_{ii}>\sum_{j\ne i}|(H_{\rm num})_{ij}|.
\tag{11}
```

All these are exact integer comparisons. The minimum row margins obtained are:

| n | d | h | minimum positive integer row margin |
|---|---:|---:|---:|
| 8 | 91 | 84 | 999999952863237952570849 |
| 9 | 120 | 112 | 999999925669481281169422 |
| 10 | 153 | 144 | 999999906716728966649869 |
| 11 | 190 | 180 | 999999874503493510818039 |
| 12 | 231 | 220 | 999999824037570658807213 |

For completeness, a real symmetric matrix H satisfying (11) is positive definite: for every real vector v,

```math
v^THv\ge\sum_i\left(H_{ii}-\sum_{j\ne i}|H_{ij}|\right)v_i^2>0
```

when v is nonzero, using 2|v_i v_j|<=v_i^2+v_j^2.

Thus H_num is positive definite. Equation (10) implies T_num has trivial kernel; being square, it is invertible. Congruence then proves G_num positive definite, and positive scaling proves G positive definite. Combining this with (9) and the spanning property of B,u_k proves Q>=0, of rank exactly h. This inference does not assume a numerically computed eigenvalue bound or the invertibility of a rounded factor.

## 5. From the Gram certificate to the required squares

Every real positive semidefinite matrix Q of rank h has a real factor R with Q=R^TR and R having h rows, by the finite-dimensional spectral theorem. Therefore

```math
z^TQz=\sum_{r=1}^{h}(Rz)_r^2.
```

Each (Rz)_r is a homogeneous quadratic polynomial in the original independent x,y variables. Add the 2n-2 explicit squares in (4). This yields at most

```math
h+2n-2=2(n-1)^2
```

squares, as asserted. This completes the finite-order proof.

An alternative constructive extraction uses G and the invertible rational matrix T=T_num/E. Put u=(B^TB)^(-1)B^Tz and v=T^(-1)u. Then z^TQz=v^T(T^TGT)v. Strict diagonal dominance expresses the latter as a sum of squares of v_i and v_i+sign(H_ij)v_j, with nonnegative rational weights. This gives explicit algebraic-coefficient quadratic polynomials without needing to assert that the individual square coefficients are rational.

## 6. Verification and reproducibility

From this directory run:

```sh
python verify_exact.py --output verification_recheck.json
```

This uses only the Python standard library. It does not import NumPy, SciPy, a semidefinite-programming solver, or any discovery script. It directly expands the canonical quartic, verifies the entire polynomial identity, checks the exact kernel identities, and proves positivity by (10)-(11).

The saved `verification_results.json` records successful checks and SHA-256 hashes. Floating-point search and rationalization code is retained in `discovery/` solely to explain how the certificates were obtained. Proof validity depends on the exact verifier and certificate data, not convergence of the search.

## 7. Scope relative to the original problem

The original MI-15 target quantifies over every n>=2. The certificates settle five specified instances beyond the through-order-seven certificate strategy described by the canonical README. They do not supply an induction, an all-order formula for Q, or a proof that the search succeeds for arbitrary n. Consequently MI-15 must not be marked solved on the basis of this pack.

No external human review, proof-assistant certification, upstream acceptance, or exhaustive priority search is claimed. The finite-order arguments and exact arithmetic are ready for adversarial verification.

## Source

Canonical target: https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/matrix-inequalities-and-norms/MI-15/README.md

README blob observed: `b7f7514ac5b4f2f7321b9d104f970b1fe62b695d`.

The general source is L. László, *Sum of squares representation for the Böttcher-Wenzel biquadratic form*, arXiv:1207.6372. This proof does not invoke the correctness of any previous floating-point certificate.
