# Independent review of the retained reciprocal profile bound

Root read the complete ProfileSum.lean source by /root/independent_math_review,
SHA-256 `90a9ac674a1b98065cd651d252195bbf2f5345687135d54847db79bc311a4825`,
and independently compiled it on the pinned runtime. All seven kernel checks
passed with only foundational axioms and no warnings.

The finite reindex d=t-i-1 is a bijection from the retained singular indices
to r<=d<t. The lower profile is strictly positive by the positive g(r),
positive r, and ratio hypothesis, so taking reciprocals is sound. The
finite telescoping inequality d^-2<=2(d^-1-(d+1)^-1) yields the literal
2/r upper bound without an infinite series or computation. Squaring and
summing the reciprocal bounds gives exactly 2r/g(r)^2. Empty retained
ranges are explicitly discharged. The scalar-recursion specialization uses
its already proved ratio monotonicity. Approved exact statement and proof.
