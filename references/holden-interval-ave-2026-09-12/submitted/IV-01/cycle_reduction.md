# Reduction to the cyclic part of the fixed-entry graph

This lemma strengthens the graph obstruction analysis; it does not remove that obstruction.

Use F0,F1 and the directed graph from `result.md`. Contract its strongly connected components to obtain its directed acyclic condensation graph. Choose nonnegative integer heights h on the components that strictly increase along every condensation edge, and give each row/column vertex the height of its component.

For t>0 set

    B(t)_ij = B_ij (1+t)^(h(R_i)-h(C_j)).

This is again positive row/column scaling of B. Thus it preserves nonsingularity, every zero minor, and every nonzero minor sign of B.

For a nonzero fixed entry whose graph edge joins different components, its checker gap becomes strictly positive by the orientation argument in Theorem G. For an edge within a component, the exponent is zero, so the entry stays exactly fixed. Zero fixed entries also remain zero. Original nonfixed gaps remain strictly positive for sufficiently small t.

An edge lies within a strongly connected component if and only if it belongs to a directed cycle: one direction follows from the rest of the cycle; in the other direction use a directed return path within the component. Hence, for sufficiently small t, the nonzero fixed edges of the perturbed interval are exactly the original edges belonging to directed cycles. There are no newly fixed nonzero entries.

Now suppose the original interval were a counterexample to IV-01. Lemma N and `order_two_reduction.md` rule out loss of nonsingularity and confine failure to a strictly wrong-sign minor of order 3,...,n-2. Choose a matrix M exhibiting such a negative signed minor. Interpolate M(t) between A and B(t) entrywise using its original relative coordinates, as in Theorem G. That signed minor stays strictly negative for all sufficiently small t, by continuity. Thus the perturbed interval is also a counterexample, with all noncyclic nonzero fixed edges removed. For rational endpoints and a rational witness M, rational positive t retains rationality because the exponents are integers.

**Conclusion.** Any counterexample can be reduced to one whose nonzero fixed edges all lie on directed cycles, without introducing new fixed zeros. This is a search normal form, not an assertion that a counterexample exists.

## Cycle parity

When epsilon_1=+1, the four vertex types follow the directed order

    R_even -> C_odd -> R_odd -> C_even -> R_even.

For epsilon_1=-1 all arrows reverse. Therefore every directed cycle has length divisible by four. A fixed 2 by 2 rectangle with opposite row parities and opposite column parities is the smallest possible cycle. Longer cycles need not contain such a rectangle.

## Important limitation

Cycles only obstruct the chosen diagonal scaling strategy. For example A=B equal to any positive strictly sign-regular 5 by 5 matrix has many fixed-entry cycles, yet its singleton interval is valid. Likewise, fixed zero entries of both parities survive all positive diagonal scalings. Neither phenomenon is a negative resolution of IV-01.
