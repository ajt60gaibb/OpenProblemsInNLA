# AV-03: exact scalar shooting for a structured subclass

**Repository-target classification: NEW PARTIAL RESULT.** The unrestricted problem is not resolved. The main theorem below has a complete proof candidate for an additional structural hypothesis. Historical priority of this subclass theorem has not been established; the classification records mathematical progress in this run, not a verified novelty claim.

## 1. Exact repository target and scope

For every integer n >= 1, the input is a rational n by n matrix A and rational vector b, encoded in binary. The promise is that every A - diag(d), d in [-1,1]^n, is nonsingular. No certificate is given. The target is an exact rational solution of A x - |x| = b in a number of deterministic Turing bit operations polynomial in the entire input length. Absolute values are componentwise. Behavior outside the promise is unrestricted. Strong polynomiality is not required.

Source: [canonical AV-03 README](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/intervals-and-absolute-value-equations/AV-03/README.md), blob `7f68574d70d282abedb27d00315db95ab1436324`, checked 2026-09-12.

**Additional hypothesis for the result here:** A is lower Hessenberg: a_ij = 0 whenever j > i+1. No bound on its condition number, coefficient magnitudes, or number of sign regions is added. Zero superdiagonal entries are allowed. This restriction is essential to the proof and is not a consequence of the repository promise.

## 2. Main theorem

**Theorem H.** On the promised rational lower-Hessenberg inputs just described, `hessenberg_solver.py` computes the unique exact solution in deterministic polynomial bit complexity.

### 2.1 A rational separation bound

Let q be a positive common denominator of all entries of A and b. Choose the integer

    h = max(1, q, max_ij (|q a_ij| + q), max_i |q b_i|),
    D = n! h^n.

For any selector s in {-1,1}^n, q(A-diag(s)) is an integer nonsingular matrix with entries of magnitude at most h. Its determinant is a nonzero integer of magnitude at most D, by the Leibniz formula. The same bound applies to each Cramer numerator for right-hand side qb. Thus a solution of this selected linear system has each coordinate of magnitude at most D; every nonzero coordinate has magnitude at least 1/D. In reduced form its denominator is at most D.

In particular these bounds hold for the AVE solution x*: choose s_i = sign(x*_i) when x*_i != 0 and choose either sign otherwise. Then |x*| = diag(s)x*.

The bit length of q is at most the sum of the input denominator bit lengths. Hence log h and log q are polynomial in the input length, as is log D = O(n log n + n log h). The integer D need not be polynomial in value.

### 2.2 The irreducible Hessenberg case

First suppose a_i,i+1 != 0 for every i < n. Set x_1(t) = t and recursively define

    x_(i+1)(t) = [b_i - sum_(j=1)^i a_ij x_j(t) + |x_i(t)|] / a_i,i+1,
    i = 1,...,n-1.

Define

    g(t) = sum_(j=1)^n a_nj x_j(t) - |x_n(t)| - b_n.

Every x(t) satisfies the first n-1 AVE equations. The functions x_i and g are continuous, piecewise affine functions with finitely many pieces. Their number of pieces need not be polynomial.

**Injectivity of g.** Take t != u and v = x(t)-x(u). For every coordinate with v_i != 0, put

    d_i = (|x_i(t)| - |x_i(u)|) / v_i.

Then d_i is in [-1,1]. For v_i = 0 set d_i = 0. Subtracting the equations defining x(t), x(u) gives

    (A-diag(d))v = (0,...,0,g(t)-g(u))^T.

If g(t)=g(u), regularity implies v=0, contradicting v_1=t-u. Therefore g is injective. A continuous injective real-valued function on the real line is strictly monotone. This elementary conclusion does not assert convexity or a quantitative condition-number bound.

Existence of x* is part of the repository promise. Alternatively, in this structured case, g has affine tails. Neither tail slope can be zero, by injectivity; strict monotonicity makes their slopes have the same sign, so g is onto. This independently establishes a unique zero.

The first coordinate t* of x* belongs to [-D,D]. Consequently g(-D-1) and g(D+1) are nonzero and have opposite signs. Bisection works without knowing whether g is increasing or decreasing: retain the endpoint sharing the midpoint's sign.

### 2.3 Polynomial precision suffices, including zero coordinates

Choose an integer

    C >= max(2, max_ij |a_ij|, max_(i<n) 1/|a_i,i+1|),
    B0 = (n+1) C^2,
    K = B0^(n-1).

For every real t,u,

    |x_i(t)-x_i(u)| <= B0^(i-1) |t-u|.

Proof: the case i=1 is exact. If the bound holds through i, the recursion and ||r|-|s|| <= |r-s| give

    |x_(i+1)(t)-x_(i+1)(u)|
      <= C (i C + 1) B0^(i-1) |t-u|
      <= B0^i |t-u|.

Thus the maximum coordinate error is bounded by K|t-u|. Bisect until the interval width is at most 1/(2DK), and let t_hat be its midpoint. Then

    ||x(t_hat)-x*||_infinity <= 1/(4D).

For every nonzero x*_i, the lower bound |x*_i| >= 1/D shows that x_i(t_hat) has its correct sign. If x*_i=0, either selected sign is valid. Set s_i=+1 for x_i(t_hat)>=0 and s_i=-1 otherwise, then solve

    (A-diag(s))z=b

exactly. The matrix is nonsingular by the promise. Since |x*|=diag(s)x*, uniqueness of this linear system gives z=x*. The implementation also checks the exact AVE residual as a defensive assertion.

The number of bisections is at most the ceiling of

    log2(4D K(D+1)).

Both log D and log K are polynomial in input length. No minimum distance between t* and all breakpoints is required. In particular, the argument covers a root at one or several breakpoints.

### 2.4 Bit complexity, not only arithmetic complexity

All bisection points are dyadic rationals with polynomially many bits. Write q a_ij and q b_i as integers. The shooting recursion becomes

    x_(i+1) = [q b_i - sum_(j<=i) (q a_ij)x_j + q|x_i|] / (q a_i,i+1).

At a dyadic t of denominator 2^k, an induction shows that the denominator of x_i(t) divides

    2^k product_(r<i) |q a_r,r+1|.

The bit length of this product is O(k+n log h). Magnitudes of the intermediate coordinates have a polynomial logarithmic bound as well: using the same C and B0,

    max_(j<=i+1) |x_j(t)| <= B0 max_(j<=i)|x_j(t)| + C max_j |b_j|,

and |t| <= D+1. Iterating this inequality takes only n steps; its logarithm is polynomial in the input length. Hence numerators and denominators in every evaluation have polynomial bit length, not exponentially many bits despite the possible exponentially many affine regions.

Each evaluation uses O(n^2) rational arithmetic operations. Reduced-fraction addition, multiplication, comparison, division and gcd are polynomial-time integer operations at these bit lengths. The final nonsingular rational linear system is also solvable in polynomial bit complexity; for Gaussian elimination with row pivoting, its intermediate Schur-complement entries are ratios of minors and have polynomial bit bounds. Fraction-free elimination could be substituted without changing the algorithm.

This proves deterministic polynomial bit complexity for the irreducible case. The proof does not treat unit-cost operations on unbounded integers as constant time.

### 2.5 Zero superdiagonal entries

A zero a_i,i+1 in a lower-Hessenberg matrix separates a block lower-triangular decomposition into contiguous diagonal blocks. Each diagonal block is itself a regular diagonal family: if one block had a singular selected member, extending its diagonal choice arbitrarily to the other blocks would make the whole block lower-triangular matrix singular.

Solve the blocks in order. Subtract the already determined preceding coordinates from the next block's right-hand side and apply the irreducible algorithm. A block of size one is included. The resulting vector solves all equations exactly.

These successive right-hand sides still have polynomial encoding length. Each already determined coordinate is a coordinate of the global unique solution, with numerator and denominator bounded by the global Cramer bounds above; sums of at most n products therefore have polynomial bit length. There are at most n blocks. This completes the proof of Theorem H.

## 3. An exponential sign-region family within the solved subclass

For n>=2, take the only nonzero entries of A to be

    a_i,i+1 = -1/2  (i<n),       a_n1 = 2^n.

For all d in [-1,1]^n the determinant is

    det(A-diag(d)) = 2 + (-1)^n product_i d_i,

because the only possible determinant permutations are the diagonal and the full cycle. It lies in [1,3], so this is a regular family. Set b_i=-1/2 for i<n. The shooting recurrence is the tent map

    x_1=t,       x_(i+1)=T(x_i),       T(z)=1-2|z|.

The last right-hand side is beta(t)=2^n t-|x_n(t)|. Since T^(n-1) is 2^(n-1)-Lipschitz,

    beta(t)-beta(u) >= 2^(n-1)(t-u) > 0  whenever t>u.

Every one of the 2^n strict sign patterns occurs for t in (-1,1). Indeed, for any chosen s_1,...,s_n in {-1,1}, set x_n=s_n/2 and work backwards by

    x_i = s_i(1-x_(i+1))/2.

Each coordinate stays in (-1,1), has the prescribed nonzero sign, and obeys T(x_i)=x_(i+1). A strict itinerary persists on an open interval by continuity. A fixed itinerary determines affine x_i(t), and its strict sign inequalities cut out an interval, so it cannot have two disconnected components. Hence there are exactly 2^n strict itinerary intervals.

As beta varies from -2^n-1 to 2^n-1, its unique solution traverses all these patterns. Any continuation procedure that processes every visited orthant separately therefore has an exponential number of regions to process on this family. This is **not** a lower bound against all algorithms: Theorem H solves the same family in polynomial bit complexity, without tracing its regions. Nor is this a counterexample to AV-03.

## 4. Exact failures of two proposed general shortcuts

Let t>0 and

    A_t = [[1,t,0],[0,1,t],[t,0,1]],       b=(-2,-2,-2)^T.

For every diagonal d in [-1,1]^3,

    det(A_t-diag(d)) = product_i(1-d_i)+t^3 > 0.

The family is regular for every t>0. Its AVE solution is -2/(2+t) times the all-ones vector.

### 4.1 A three-cycle of undamped sign Newton

At the selector s=(-1,-1,+1), the selected solution is

    y = (-2/t, (4-2t)/t^2, (-2t^2+4t-8)/t^3)^T.

For 0<t<2 its sign is (-1,+1,-1). Cyclic rotation gives the next two selected solutions and returns to the original selector. The last numerator is always negative because -2t^2+4t-8=-2((t-1)^2+3). Thus all coordinates in this cycle are nonzero and there is no tie-breaking issue.

For t=1/2 the selected vectors are

    (-4,12,-52),   (12,-52,-4),   (-52,-4,12).

This disproves convergence of the undamped sign-Newton iteration under the promise alone. It says nothing negative about algorithms with an independently proved globalization procedure.

### 4.2 Convex separation of all inverse images can fail

At t=1/2, take the four selectors

    (-1,-1,-1),  (-1,+1,+1),  (+1,-1,+1),  (+1,+1,-1).

Their inverse images (A_t-diag(s))^(-1)b are respectively

    (-4/5,-4/5,-4/5),  (-4,12,-4),  (-4,-4,12),  (12,-4,-4).

Their weighted sum with weights (5/8,1/8,1/8,1/8) is zero. Therefore no linear functional strictly separates zero from all these admissible inverse images. Equivalently this convex combination of the inverse matrices is singular: it annihilates b!=0.

More generally the same four selectors give a zero convex combination for 0<t<=2/3, with the last three weights equal to

    beta=t^2/[4(1-t)]

and first weight

    alpha=(2-3t)(t+2)/[4(1-t)].

They are nonnegative, sum to one, and the coordinate sum cancels directly. This defeats an interval-wide inverse-image separation shortcut. A secant diagonal compatible with a specified iterate and its unknown solution may satisfy additional restrictions; this example does not rule out a more informative separation oracle.

## 5. Why the original target remains open in this pack

The polynomial solver requires a one-dimensional shooting parametrization. An arbitrary dense A has no such triangular recurrence. An orthogonal Hessenberg reduction does not fix this: absolute values do not commute with a general change of basis. No polynomial construction of an equivalent structured system preserving the diagonal absolute-value form is proved here.

Sections 3-4 rule out only specified algorithmic approaches. They do not prove that a polynomial algorithm for the original promise problem is impossible. Additional general lemmas and the exact P-LCP reduction are in `general_reductions.md`.

## 6. Verification files

Run `python AV-03/test_solver.py` from the pack root. It includes 108 exact tests covering scalar cases, reducible blocks, zero coordinates, tiny nonzero rational coordinates, non-diagonally-dominant promised matrices, and the exponential-region family. The finite tests support the implementation; Theorem H is justified by the argument above, not by those tests.

Run `python AV-03/verify_obstructions.py` to check the displayed rational certificates and all tent-map itineraries through the recorded test dimensions.

## 7. Exact optimized-handicap analysis

`optimized_handicap.md` proves the exact formula
kappa*(I+aP)=max(0,(a^2-4)/16) for the 3-cycle P and all a>=0, including the
infimum over positive diagonal scalings. The lower bound is uniform over all
such scalings, and the upper bound is an exhaustive real-variable sign-case
proof. This supplies an explicit exponentially large optimized parameter in
binary input length on a family whose AVEs are nevertheless solved by Theorem H.
It is a complete family-level proof candidate, not a resolution of AV-03.
