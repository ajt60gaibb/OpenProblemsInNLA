# Exact Gaussian column splitting and pivot fibers with fresh columns

Proposed by root before implementation. For t<=n, split the actual square
Gaussian matrix into its n by t prefix and n by (n-t) suffix in original
column order. The joint law is the product of the two actual rectangular
Gaussian laws. An explicit measurable assembly map is the inverse of this
coordinate split. Also split a rectangular n by (a+b) Gaussian block into
its first a and last b columns with exact product law.

For a fixed pivot-order injection pi of length t, combine this column law
with the already proved F7 restricted law: after restricting the square
matrix measure to orderEvent(pi), its map to
(selected T, remaining prefix rows Z, full fresh suffix W) is exactly the
product of the F7 restricted (T,Z) law and the n by (n-t) Gaussian law.
Equivalently, every jointly measurable nonnegative test has the iterated
integral over Good(T), weight q(T)^(n-t), independent normalized remaining
prefix rows, and independent fresh Gaussian suffix columns.

The pivot order depends only on the first t columns. No conditioning on
future pivot success is introduced. All endpoint cases t=0,t=n and a=0
or b=0 retain literal empty matrix/product measures. These are coordinate
law identities, with no new numerical probability estimate.
Independent preimplementation review is required.

Independent preimplementation review by /root/source_statement_author:
Approved. The coordinate bijection preserves the exact iid product law;
orderEvent is a prefix event, so restriction factors with the full suffix.
F7's tested law composes by Tonelli, retaining the exact weight. All empty
endpoint products are valid.
