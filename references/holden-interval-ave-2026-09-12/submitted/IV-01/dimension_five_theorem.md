# A stronger dimension-five theorem, including cyclic fixed graphs

**Status:** complete proof candidate for an additional sufficient condition,
not a resolution of unrestricted IV-01. This theorem is self-contained given
the elementary Lemma N and the order-two reduction proved elsewhere in this
pack; it does not use the external same-parity theorem. Historical novelty
has not been established.

## Theorem V

Under the original IV-01 hypotheses, suppose:

1. No scalar entry interval is the singleton {0} (there are no fixed zero entries).
2. Every 2 by 2 submatrix on consecutive rows and consecutive columns whose
   four entries are all fixed has nonzero determinant.

Then every matrix in the interval has the required order-three minor signs.
Consequently, **for n=5 the entire conclusion of IV-01 holds.**

For n>5 this theorem controls order three, not every remaining middle order.
For n=5 the hypotheses permit directed fixed-entry cycles: a fully fixed
adjacent 2 by 2 rectangle is allowed when its determinant is nonzero.

## 1. Normalization and the relative interior

As in `order_two_reduction.md`, negate the matrices if necessary and reverse
all rows if necessary, swapping checker endpoint roles as appropriate. These
operations make the entry and order-two signs positive. They transform the
higher signature in a fixed, known way; negation multiplies an order-k minor
by (-1)^k, and row reversal by (-1)^(k(k-1)/2). Adjacency, fixed zero entries,
and singularity of fully fixed adjacent blocks are preserved. We therefore
work with nonnegative entries and nonnegative order-two minors, with the
normalized required order-three sign denoted by eta in {-1,1}.

The order-two theorem proves nonnegative order-two minors at **every** matrix
of the interval. Lemma N proves nonsingularity and the signs at orders n-1,n.

Take M in the relative interior of the box: every nonfixed scalar coordinate
is strictly between its two bounds. Every entry of M is positive. Indeed a
fixed entry is nonzero by hypothesis and nonnegative by normalization; a
nonfixed nonnegative scalar interval has positive relative-interior points.
No strictness of endpoint entries is needed.

## 2. Adjacent order-two minors are strictly positive in the relative interior

Consider an adjacent 2 by 2 block of M. Its determinant is nonnegative by the
order-two theorem. If the four entries are fixed, its determinant is nonzero
by hypothesis, hence positive. Otherwise choose a nonfixed entry of the block.
If its determinant were zero, change just that entry by a sufficiently small
amount in the determinant-decreasing direction. This is permitted because
M is in the relative interior. The cofactor of the chosen entry is a signed
single entry of M, and hence nonzero. Dependence on that entry is exactly
affine, so this change would make the determinant strictly negative. That
contradicts the order-two theorem. The adjacent determinant is therefore
positive in this case too.

Since every entry of M is positive, multiplication and cancellation of the
adjacent inequalities on any rectangular index range, as in the order-two
proof, shows that **every order-two minor of M is strictly positive**. For
any pair of distinct rows and columns the rectangle contains at least one
adjacent inequality, and here all of them are strict.

## 3. Every adjacent order-three minor has the required weak sign

Fix consecutive rows I=(i,i+1,i+2) and columns J=(j,j+1,j+2). Consider the
signed minor eta det X[I,J] as a function of the checker coordinates of X
on the entire original box. Its partial derivative at an entry (i+a,j+b)
inside the block, with a,b in {0,1,2}, is

    eta (-1)^(a+b) det X[I without (i+a), J without (j+b)].

All the displayed order-two minors are nonnegative throughout the box.
A positive change in checker coordinate changes the original entry by
(-1)^(i+j+a+b) times that change. Therefore every nonzero derivative of this
signed order-three minor with respect to a checker coordinate has the same
weak sign

    eta (-1)^(i+j).

The function is coordinatewise monotone in one common direction. Integrating
one coordinate at a time, its minimum on the box is attained at one of the
two checker endpoints A or B. Both endpoints have the required order-three
sign. Hence every adjacent order-three minor is correctly weakly signed,
including at the relative-interior matrix M.

## 4. A strict-order-two propagation lemma

**Lemma.** Let X have positive entries and all order-two minors strictly
positive. If all its adjacent order-three minors have the same weak sign
eta, then every order-three minor has that weak sign.

**Proof.** Fix three consecutive columns c1<c2<c3. Divide each row of these
three columns by its positive first entry, obtaining row vectors

    (1,u_i,v_i),
    u_i=X_i,c2/X_i,c1,  v_i=X_i,c3/X_i,c1.

Strict positivity of the order-two minors on columns c1,c2 implies that u_i
strictly increases with i. Write

    s_i=(v_(i+1)-v_i)/(u_(i+1)-u_i).

For consecutive row triples, the sign of the normalized determinant is the
sign of s_(i+1)-s_i: its positive factor is
(u_(i+1)-u_i)(u_(i+2)-u_(i+1)). Therefore eta s_i is nondecreasing.

For any i<j<k, the secant slope from i to j is a weighted average of
s_i,...,s_(j-1), with strictly positive weights u_(r+1)-u_r. The slope from
j to k is a weighted average of the later slopes s_j,...,s_(k-1).
Their eta-weighted order is therefore the same. The determinant on rows
i,j,k has sign eta or is zero. Thus all row triples are correctly signed
for every fixed consecutive column triple.

Now fix any three rows and apply the same argument to the transpose of their
3 by n submatrix. Its entries are positive and the ratios formed from the
first two chosen rows strictly increase with column index, by strict
order-two positivity. All its consecutive triples have just been proved
correctly signed. The secant-slope argument proves the sign for every column
triple. This establishes the lemma. No third-order minor is assumed nonzero.

Applying the lemma to the relative-interior M proves all its order-three signs.

## 5. Closure and the dimension-five conclusion

Any matrix N of the box is a limit of relative-interior matrices, for example
(1-t)N+tC as t decreases to zero, where C is the entrywise midpoint of the box.
If the box is a singleton, C is itself its relative interior; the same argument
applies. Determinant continuity passes all the weak order-three signs to N.
Nonsingularity at N follows independently from Lemma N, not from the limit.

Undoing the normalization proves Theorem V. When n=5, the controlled orders
are 1,2,3,4,5, so the full nonsingular SR conclusion follows. For larger n,
orders 4,...,n-2 may still be missing. This is not claimed to resolve them.

## Counterexample-search consequence

A five-dimensional counterexample must contain either a fixed zero entry or
a singular fully fixed adjacent 2 by 2 block (possibly both). Combined with
the graph/SCC reductions, this is a substantially narrower boundary search.
It is a necessary obstruction for a counterexample, not a claim that such
an obstruction produces one. Singleton intervals with a singular fixed
2 by 2 subblock illustrate why the conditions are not necessary for validity.
