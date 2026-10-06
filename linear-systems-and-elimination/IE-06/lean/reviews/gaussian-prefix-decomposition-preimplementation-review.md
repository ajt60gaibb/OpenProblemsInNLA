# Fixed selected-prefix decomposition: approved implementation interface

Root approved the exact B1+B2 stage contract before this bounded implementation.
For fixed ht:t<=n, fixed injection pi:Fin t→Fin n, Good(T), 1<=r<t, x>0,
and sigmaInvSum(T,r)<=tau, let A0(Z)=restore ht pi ((T,Z),0). The row law is
the literal finite product over RemainingRows(pi) of the normalized Gaussian
restriction to truncationBody(T).

First prove almost surely that every remaining row is in the strict body:
normalization of the proved closed-minus-strict null set gives the scalar
claim, and exact product evaluation plus finite conjunction gives all rows.
The existing strict-fiber theorem then proves the actual pivot order of A0
is pi. Good(T) gives exactly PrefixNonzero, since restore reproduces T.
No property of later pivots or global nonsingularity is imposed.

Choose R,H,V once for this fixed T using the proved genuine inverse
decomposition: V^T V=I, T^-1=R+HV^T, and frobeniusNorm(R)^2=sigmaInvSum(T,r).
The already proved original-coordinate embedding then gives Q=P_pi V with
Q^TQ=I, and almost surely E_t(A0)=retainedRows(A0,R)+discardedRows(A0,H)Q^T.
The public existential theorem will package these identities and the following
literal event bound.

A reusable intermediate takes ANY fixed R with frobeniusNorm(R)^2<=tau.
On the almost-sure pivot-order event, an active row's original label lies
outside pi, and its first t entries are exactly the corresponding Z row.
Thus rowNorm(retainedRows)^2=1+norm(Z_row*R)^2. Inactive rows vanish. The bad
row-norm event above sqrt(1+(2+4x)tau) is therefore contained almost surely in
the finite-row quadratic bad event already proved by GaussianTruncatedRows.
Its probability is at most (n-t)*exp(-x), hence at most n*exp(-x). The sqrt
argument is nonnegative because tau>=frobeniusNorm(R)^2>=0.

No measurable choice of R,H,V as T varies is asserted. The choice is fixed
inside each T fiber and the eventual public stage event remains intrinsic.
The exact formulas, count n, and threshold are those explicitly approved by
root. This module alone does not claim the completed stage smoothing theorem.

## Completed implementation

Root additionally requested and approved measurability of the actual canonical retained-row bad set before its implementation. The module proves it for every fixed R, using a finite path parameter and fixed-path polynomial formulas; no spectral selector is assumed measurable.

Frozen source SHA-256: `55607ded854193e111aeb286a17ed4352de6def0166f01580495bf3dbe78c445`. Twelve declarations each have a kernel trust assertion and an axiom print. The pinned local build completed without errors or warnings, with only the standard foundational axioms. The compiler output and scope-qualified receipt are in `gaussian-prefix-decomposition/`. Independent final source review remains the parent's separate task.
