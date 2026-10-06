# Independent preimplementation review: smoothing stage split

Approved root's simpler exact staging before B1+B2 assembly. For natural
r and any final stage u>5r with u<=n, set t=u-4r. Then t>r and t+4r=u<=n.
The retained-inverse construction applies with discarded rank exactly r,
and the future block contains exactly 4r original fresh columns. For u<=5r,
the existing row-l1 bound yields the Euclidean row norm <=2^u<=2^(5r).
No t<=r truncation branch or measurable minimum-rank selector is needed.
At r=ceil(sqrt(log n)), changing the early-stage constant from 4r to 5r
only changes a dimension-independent constant in the final exponential;
the same original IE-06 and subpolynomial upper-tail targets remain. If n
is small relative to r the entire stage range uses the deterministic branch;
large-dimension asymptotic assembly may restrict n as already authorized.
The number of candidate final stages remains at most n, so no additional
probability factor is introduced by this reindexing.
