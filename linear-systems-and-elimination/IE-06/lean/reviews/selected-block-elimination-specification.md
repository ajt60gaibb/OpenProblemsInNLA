# Exact selected-block representation of the elimination rows

Proposed by root before implementation. Let A be a nonsingular n by n real
matrix and 0<=t<=n. Use the actual canonical firstPath, its accumulated
permutation rowLabels, and pi=pivotOrder ht A from GaussianPivotConditioning.
Let T=selectedBlock ht pi A and E=eliminationRows A (firstPath A) t.

Prove T.det != 0 (including t=0). For every active current row i>=t, put
label=rowLabels(firstPath A)t i and z=(A(label,j)) for original columns j<t.
Then label is not in range(pi), and for every original coordinate j,

  E(i,j) = indicator(j=label) -
           sum_{a:Fin t} (z * T^(-1))(a) * indicator(j=pi(a)).

Inactive rows i<t are exactly zero, as already proved. This is an equality
in original input coordinates, with no hidden row permutation or discarded
coordinate. In particular the square norm of an active E row is
1+||z*T^(-1)||_2^2, since its identity coordinate lies outside the selected
labels. A decomposition T^(-1)=Z+H V^T can therefore be embedded in the
original n coordinates to produce the exact X,Y,Q required by smoothing.

The immediate implementation scope is nonsingularity, the displayed row
identity, and its square norm. No random measurable singular-vector choice
is claimed. All original Gaussian nonsingularity exceptions will be handled
by their already proved null measure when applying this deterministic result.
Independent review is required before implementation.
