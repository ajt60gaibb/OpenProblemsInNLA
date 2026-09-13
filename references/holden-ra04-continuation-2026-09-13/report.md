# RA-04: narrow-band stability and exact-tail deflation

**Author:** Sidney Holden  
**Affiliation:** Center for Computational Biology, Flatiron Institute, Simons Foundation  
**Role:** Flatiron Research Fellow, Biological Transport Networks  

**Partial results. The unrestricted RA-04 iteration bound is not established.**

## 1. Target and relation to the previous report

Let A be an n by d real matrix, M = A A^T, and let its eigenvalues be
lambda_1 >= ... >= lambda_n >= 0. Set t = ceil(k/b), m = bt <= rank(A),
and Delta = min_{1 <= i <= m-b}(lambda_i-lambda_{i+b})/lambda_i > 0.
When m=b, use the empty-minimum convention Delta=1. The Gaussian block G has
n rows and b independent standard-normal columns. The Krylov space K_q is the
span of G, MG, ..., M^(q-1)G. The output is Z[Z^T A]_k for an orthonormal basis Z.

RA-04 requests the iteration order

    q = O((t log(2/Delta) + log(n/(delta epsilon))) / sqrt(epsilon)).

The previous report obtained a general bound with t log(2m/Delta) instead of
t log(2/Delta), and established the requested order in several restricted cases.
This continuation does not remove the extra logarithm for arbitrary inputs.
It proves a nonzero-width extension of the exact-cluster case and a separate
exact-recovery result for low tail spectral diversity.

The main new graph theorem is self-contained. Its translation to the three
approximation guarantees is an explicitly imported good-start convergence
principle, the same dependency used in the previous report. No raw monomial
matrix condition-number estimate is substituted for a subspace estimate.

## 2. A Gaussian block estimate

If H is an a by b standard Gaussian matrix with a <= b, then for u >= 0,

    P(sigma_min(H) <= u) <= 16 sqrt(a) u.

Here is an elementary proof. Let v be a unit left singular vector for the least
singular value, with an independent random sign. Gaussian orthogonal invariance
makes v uniform on the unit sphere and independent of the singular values.
For one fixed coordinate, E[v_i^2]=1/a and E[v_i^4]=3/(a(a+2)). The
Paley-Zygmund inequality gives P(|v_i| >= 1/sqrt(2a)) >= 1/12.

Let D_i be the distance of row i from the span of the other rows. The identity
D_i^(-2) = ((HH^T)^(-1))_ii implies D_i <= sigma_min(H)/|v_i|.
Conditioned on the other rows, D_i has a chi distribution with b-a+1 degrees
of freedom; consequently P(D_i <= z) <= sqrt(2/pi) z. Combining these facts
bounds the probability in question by (24/sqrt(pi)) sqrt(a) u, which is at
most 16 sqrt(a) u. Repeated singular values occur with probability zero, so
there is no ambiguity in the argument.

For r Gaussian blocks H_s having at most b rows each, a union bound therefore
shows that all their least singular values exceed eta/(16r sqrt(b)), except
on an event of probability eta. No independence between this event and any
subsequent perturbation is required.

## 3. Barycentric scaling without a leading condition number

Partition the first m indices into r consecutive nonempty groups J_s, each
having at most b members. Choose centers c_1 > ... > c_r > 0, and define

    beta = min_{s<r} (1-c_{s+1}/c_s).

Assume r >= 2 and |lambda_i-c_s| <= w c_s for i in J_s. Define

    p_j(x) = product_{ell != j} (x-c_ell),
    d_s = product_{ell != s} (c_s-c_ell).

The signs of d_s are retained. At a center, p_j(c_s)/d_s equals the Kronecker
delta. For an actual node in group s, set v_ij = p_j(lambda_i)/d_s.
If rw/beta <= 1/2, then

    ||v_i - e_s||_2 <= 2r w/beta.

To verify this, for the diagonal entry write each factor as
1+(lambda_i-c_s)/(c_s-c_ell). Every perturbation has absolute value at most
w/beta. The product differs from one by at most 2(r-1)w/beta.
For j != s, isolate the factor (lambda_i-c_s)/(c_s-c_j); the remaining
product is bounded by exp((r-2)w/beta) <= 2. The squared row error is at most
4r(r-1)(w/beta)^2, giving the displayed bound.

There is also a tail normalization estimate:

    max_{j, 0<=x<=(1+w)c_r} |p_j(x)| / min_s |d_s|
        <= ((1+w)/beta)^(r-1).

Indeed, the numerator is at most (1+w)^(r-1) product_{ell<r} c_ell.
For each s, pairwise separation gives

    |d_s| >= beta^(r-1) (product_{ell<s}c_ell) c_s^(r-s)
           >= beta^(r-1) product_{ell<r}c_ell.

The ratio c_1/c_r cancels. This cancellation is why unscaled perturbation of
a monomial Vandermonde matrix is not used here.

## 4. Main graph-subspace theorem

Write G in the eigenbasis of M as [H; T], where H contains the first m rows.
Let eta = delta/3. Under the band assumptions of Section 3, suppose

    w <= beta eta^(3/2) / (64 r^2 b sqrt(m)).                 (W)

Then, with probability at least 1-delta, K_r contains the columns of
U[I_m; F] for a matrix F satisfying

    ||F||_F <= 32 b r^(3/2) sqrt(n-m) eta^(-3/2)
               ((1+w)/beta)^(r-1).                         (G)

When n=m, the tail is empty and the right side is zero.

### Proof

Use the polynomial basis p_1,...,p_r rather than monomials. The head row for
i in group s is the concatenation of p_j(lambda_i) h_i^T. Divide this row by
d_s and call the resulting matrix C. Its centered counterpart C_0 is block
diagonal, with diagonal blocks H_s. Put E=C-C_0.

The deterministic row estimate gives

    ||E||_2 <= ||E||_F <= (2r w/beta)||H||_F.

Intersect the following events: every H_s has least singular value at least
eta/(16r sqrt(b)); ||H||_F <= sqrt(mb/eta); and
||T||_F <= sqrt((n-m)b/eta). The preceding Gaussian lemma and Markov's
inequality bound their total failure probability by 3eta=delta. For an empty
tail, omit the last event.

On their intersection, R_0=C_0^dagger is a right inverse with norm at most
16r sqrt(b)/eta. Assumption (W) implies ||E R_0||_2 <= 1/2. Therefore

    R = R_0 (I_m+E R_0)^(-1)

is a right inverse of C and has norm at most 32r sqrt(b)/eta. This formula
also covers rectangular blocks; using an unjustified square inverse is not
necessary.

Let D have diagonal entry d_s on group J_s. The unscaled head is D C,
so R D^(-1) is its right inverse. Multiplying the full polynomial Krylov
matrix by this right inverse yields head I_m and tail F. Each tail row has
squared norm bounded by r max_j |p_j(x)|^2 ||g_tail||_2^2 before applying
the inverse. Apply the tail normalization estimate and the bounds on R and T
to obtain (G). All operations use polynomials of degree at most r-1, so the
constructed columns really lie in K_r. This proves the theorem.

The perturbation E is built from the same Gaussian rows as C_0. The proof
uses a deterministic norm inequality on an intersection of events; it does
not incorrectly treat E and C_0 as independent.

## 5. Consequences for RA-04

First take r=t, with exactly b eigenvalues in each band. If w <= beta/4,
comparison of consecutive bands gives

    beta/2 <= Delta <= 3beta/2.

The width condition (W) implies this restriction. Taking logarithms in (G)
therefore gives

    log(1+||F||_F^2) = O(t log(2/Delta)+log(n/delta)).

The good-start convergence transfer then establishes the requested RA-04
iteration order, with all three output guarantees, whenever (W) holds.
This is a genuine nonzero-width regime; it is not a claim for arbitrary widths.
The same consequence holds for r=O(t) unequal bands when their center gap is
comparable to Delta, but that comparability is an additional hypothesis.

### A fixed-spectrum statement for every failure probability

Let m>=2 and t>=2. Suppose the equal-size bands obey

    w <= beta / (64 * 3^(3/2) * t^2 * b * m^((3t+1)/2)).     (W_all)

For delta >= m^(-t), this implies (W). For delta < m^(-t), the previous
report's general all-input theorem supplies the result, because its extra
term t log m is then bounded by log(1/delta). Thus, using that explicitly
imported prior theorem, the requested RA-04 order holds for all delta in
(0,1) in the fixed spectral regime (W_all).

The small-width condition is intentionally visible. This corollary does not
prove that every admissible spectrum can be placed into such bands.

## 6. Generic block-Vandermonde rank

Let rho rows be assigned real nodes, with at most b rows at any one node.
For a rho by b matrix H of independent continuous random variables with
joint density, define

    V_q(H) = [H, Lambda H, ..., Lambda^(q-1) H].

If qb >= rho, then V_q(H) has row rank rho almost surely.

To prove this, assign each row one of b colors, with distinct colors within
every equal-node group and at most q rows of each color. A constructive rule
is to assign each group to the currently least-loaded distinct colors. The
maximum and minimum loads differ by at most one after every group; hence
the final maximum is ceil(rho/b).

Set a row of H equal to the coordinate vector of its color. After permuting
columns and rows, V_q(H) splits into ordinary Vandermonde blocks. Each block
has distinct nodes and no more than q rows, so it has full row rank. This
exhibits a nonzero rho by rho minor polynomial. Its zero set has Lebesgue
measure zero, proving the random statement. The witness is not an assertion
that the Gaussian matrix itself has coordinate-vector rows.

## 7. Exact recovery with few distinct lower eigenvalues

Set theta=lambda_k>0. Let a be the total multiplicity of eigenvalues strictly
above theta, and let d_theta be the full multiplicity of theta. Define

    rho = a + min(d_theta,b),
    L = number of distinct eigenvalues of M strictly below theta,

counting zero once when it occurs. Suppose all eigenvalues above theta have
multiplicity at most b and k-a <= b. These conditions follow from RA-04's
positive clustered-gap hypothesis on the first m eigenvalues.

Then, almost surely, K_{L+ceil(rho/b)} contains an optimal rank-k left singular
subspace. Consequently the prescribed projection-and-truncation output is an
exact best rank-k approximation. In RA-04 notation, rho <= m+b-1, so
L+t+1 Krylov blocks suffice. The exact iteration count is the sharper
L+ceil(rho/b), not always L+t.

For the proof, let f(x) be the product of x-tau over the L lower distinct
values. The block f(M)G has no component below theta. Its projection into each
higher eigenspace has full row rank almost surely. In the theta eigenspace,
it spans min(d_theta,b) directions. Choose min(d_theta,b) fixed coordinate
rows there; together with all higher rows these form an iid Gaussian block,
up to nonzero deterministic row scalings f(lambda).

Apply the generic rank theorem to these rho selected coordinates. The full
filtered Krylov space has accessible dimension exactly rho: additional rows
in the theta eigenspace are linear combinations of the selected rows, with
the same eigenvalue. Thus the filtered space spans every higher eigenspace
and at least k-a directions at theta. Multiplication by f adds L to the
maximum polynomial degree, giving the claimed block count. An optimal
rank-k left singular subspace is therefore contained in the original
Krylov space.

This regime permits arbitrarily large rank and arbitrary multiplicities in
the lower tail. It requires only a small number of distinct lower values to
obtain a small exact iteration count. It does not control a tail with many
distinct eigenvalues.

## 8. Why the boundary correction matters

Take b=2, k=m=4, and eigenvalues (5,4,3,2,2,2). The clustered gap is 2/5.
Here theta=2, a=3, min(d_theta,b)=2, rho=5, and L=0. The theorem gives three
blocks. Two do not generically suffice for exact recovery.

Indeed, in K_2 every lower-block coefficient has the form H_tail(u+2v).
The Gaussian H_tail has rank two almost surely. A vector in K_2 with zero
component at theta therefore satisfies u+2v=0, leaving at most two degrees
of freedom. Exact rank-four approximation requires all three eigendirections
strictly above theta. They cannot all be contained in this two-dimensional
intersection. This example is not a counterexample to RA-04's big-O bound.

## 9. Validation and its limits

The standard-library exact checker verifies the balanced-coloring witness
for a finite family of multiplicity patterns, polynomial normalization,
Neumann right-inverse identities, rational graph bounds for nonzero-width
examples, and the boundary example's ranks. Every asserted test result is
recorded in the generated results files, rather than assumed from this text.
The optional NumPy script provides floating-point graph diagnostics.

These checks detect implementation or algebra errors in finite examples.
They do not replace the proofs, independently verify the imported convergence
theorem, establish the general interpolation estimate, or certify a universal
constant for unrestricted RA-04.

## 10. What remains

Outside the stated regimes, the previous all-input estimate still carries
an extra t log m. This report neither removes that term for arbitrary cluster
widths nor proves a lower bound showing it is necessary. The sufficient
square-depth interpolation estimate in the prior report is still an open
obligation within this work. Its failure would not itself refute RA-04,
because the algorithm can use additional Krylov powers.

The appropriate mathematical status of this archive is PARTIAL.

## Sources and dependencies

[1] Open Problems in Numerical Linear Algebra, RA-04 repository entry:
https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/randomized-and-low-rank-approximation/RA-04

[2] RA04_partial_results.pdf, the prior report supplied in this conversation.
Used for the existing all-input bound, previous restricted regimes, and the
previously identified good-start convergence dependency. The previously submitted report and audit are retained at the immutable revision:
https://github.com/sidneyholden1/OpenProblemsInNLA/blob/e15ce4854d1a9c9fa457b93da78fca04febf200a/references/holden-ra04-2026-09-12/README.md.

[3] T. Chen, E. N. Epperly, R. A. Meyer, C. Musco, and A. Rao,
Does block size matter in randomized block Krylov low-rank approximation?,
arXiv:2508.06486; SODA 2026. https://arxiv.org/abs/2508.06486
The good-start convergence transfer is imported, not re-proved here.

[4] R. A. Meyer, C. Musco, and C. Musco, On the Unreasonable Effectiveness of
Single Vector Krylov Methods for Low-Rank Approximation, arXiv:2305.02535.
https://arxiv.org/abs/2305.02535

[5] N. Shao, A structural bound for cluster robustness of randomized small-block
Lanczos, arXiv:2507.10144. https://arxiv.org/abs/2507.10144
Listed as related work, not as a proof of the unresolved estimate.
