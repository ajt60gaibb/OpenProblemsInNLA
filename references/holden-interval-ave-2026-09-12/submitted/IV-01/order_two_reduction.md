# All order-two minors are already controlled

This is a self-contained useful reduction, not a resolution of IV-01 and not
a claim of historical novelty. Combined with Lemma N, it confines any failure
of the original conjecture to orders 3,...,n-2. In dimension five, only order
three remains.

## Theorem

Let A<=*B be nonsingular real square matrices of the same size n>=2. Suppose their
entries have one common weak sign epsilon_1 and all their order-two minors
have one common weak sign epsilon_2. Then every matrix between A and B in
checker order has the same weak entry and order-two signs.

The theorem does not by itself assert nonsingularity of the intermediate
matrices under only these order-one and order-two hypotheses. Nonsingularity
in IV-01 comes from the separate full-endpoint cofactor argument in Lemma N.

## 1. Normalization

Multiplying all matrices by -1 makes their entries nonnegative if necessary;
it reverses checker order, so interchange endpoint roles. This does not change
order-two minor signs. If epsilon_2=-1, reverse all rows. Each order-two minor
changes sign, and nonsingularity is preserved. Reversing rows multiplies all
checker-gap signs by the single factor (-1)^(n+1), so again interchange
endpoints if required. Thus it suffices to prove the theorem when A and B
are nonnegative, nonsingular, and have every order-two minor nonnegative.
All transformations are invertible and map the entire original interval to
the corresponding transformed interval.

## 2. Positive diagonals and staircase zero patterns of the endpoints

Let X be a nonnegative nonsingular matrix with all order-two minors
nonnegative. A nonzero determinant term supplies a permutation sigma with
all X_i,sigma(i)>0. If adjacent rows i,i+1 form an inversion
sigma(i)>sigma(i+1), their order-two minor gives

    X_i,sigma(i+1) X_(i+1),sigma(i)
       >= X_i,sigma(i) X_(i+1),sigma(i+1) > 0.

Swapping the two matched columns preserves a positive permutation product
and removes an inversion. Bubble sorting the permutation eventually gives
the identity matching. Consequently X_ii>0 for every i.

If X_ij=0 with i>j, then X_kl=0 for every k>=i and l<=j. To see this,
suppose X_kl>0. If l<j, the minor on rows j,k and columns l,j, using X_jj>0,
forces X_kj>0. For l=j that conclusion is immediate. If k=i it contradicts
X_ij=0 directly. If k>i, the minor on rows i,k and columns j,i gives

    X_ij X_ki >= X_ii X_kj > 0,

another contradiction. Transposing gives the corresponding northeast zero
propagation above the diagonal. Call these the two staircase zero properties.

## 3. Every intermediate matrix inherits the staircase properties

Let M be in the normalized checker interval. Its entries are nonnegative and
M_ii>0, because both endpoint diagonal entries are positive.

Suppose M_ij=0 with i>j. If i+j is even, the lower scalar endpoint is A_ij,
so A_ij=0. Its immediate southwest neighbors, (i+1,j) and (i,j-1) whenever
present, are zero in A by its staircase property. At these opposite-parity
positions A is the *upper* scalar endpoint, so both endpoints and M are zero.
If i+j is odd, the same argument starts with B_ij=0 and uses B as the upper
endpoint at the opposite-parity neighbors. Repeating the argument proves
southwest zero propagation for M. The identical argument with northeast
neighbors handles an above-diagonal zero.

## 4. Adjacent order-two minors and propagation to arbitrary index pairs

For consecutive rows i,i+1 and columns j,j+1, the determinant is ad-bc,
with all four entries nonnegative. If i+j is even, A gives the two lower
diagonal entries and the two upper off-diagonal entries. Hence

    det A[{i,i+1},{j,j+1}] <= det M[{i,i+1},{j,j+1}]
                         <= det B[{i,i+1},{j,j+1}].

For odd i+j the endpoint inequalities reverse. In either case this adjacent
minor of M is nonnegative.

Take arbitrary i<k and j<l. If M_il M_kj=0, then
M_ij M_kl-M_il M_kj>=0 immediately. Otherwise both cross-corner entries are
positive. Every entry of the rectangle [i,k] by [j,l] is then positive:
a zero below the diagonal would propagate southwest to M_kj, a zero above
the diagonal would propagate northeast to M_il, and diagonal entries are
already positive. All three possibilities contradict positivity.

Multiply the adjacent order-two inequalities

    M_rs M_(r+1),(s+1) >= M_r,(s+1) M_(r+1),s

for r=i,...,k-1 and s=j,...,l-1. Every factor is positive, so cancellation
is valid. The product telescopes to

    M_ij M_kl >= M_il M_kj.

This proves every order-two minor is nonnegative. Undoing the normalization
proves the theorem. No strictness of endpoint order-two minors was assumed.

## Consequence for the original target

The endpoint assumptions of IV-01 include those used here. Lemma N separately
controls nonsingularity and orders n-1,n. Therefore an original counterexample
must have a strictly wrong-sign minor of order between 3 and n-2, inclusive.
There is no assertion here that complementary inverse minors also yield the
missing order n-2: checker conjugation and inversion change the relevant
interval ordering, so that tempting additional step is not justified.
