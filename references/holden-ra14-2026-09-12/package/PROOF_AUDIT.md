# Proof scope and assumption audit

This is a reader-facing audit of the arguments in `report.pdf`, not independent
peer review or a machine-checked proof. The full statements and proofs are in the
report; this ledger highlights assumptions whose omission would change a result.

## 1. Universal k-query lower bound

The hard family is nonsymmetric: A has H^T as its first k rows and zeros in the
remaining rows, with H an n-by-k standard Gaussian matrix. Rank is k almost
surely, so the target residual is exactly zero. Both oracle directions are
included: they reveal H^T x and Hc. Conditional Gaussian completion is justified
inductively for adaptive queries, not assumed only for nonadaptive queries.
With fewer than k products there remains a nontrivial Gaussian block, and the
output cannot identify the exact row space. The output's arbitrary dependence
on the transcript is included by conditioning on that transcript. Measurability
is assumed so that the algorithm's success probability is defined.

This is not a rank-one-projector direct-sum argument. Such a construction could
be queried in parallel and would not establish the claimed k dependence.

## 2. Upper bounds

The exact n-query cap reconstructs all columns. The faster bound imports the
spectral block-Krylov theorem. A block with b columns costs b products. The
right-sided implementation includes all products needed for Ritz compression;
it does not compute a hidden dense A or A^T A for free. The stated bound does not
claim optimality outside the proved matching regimes.

## 3. Warm-start theorem

The theorem assumes symmetry, positive leading eigenvalues, tail magnitude at
most b, the gap a >= (1 + 3 epsilon/2)b, and a valid starting residual at most
(1 + epsilon)b. It is not a guarantee for an arbitrary initial block.

For b > 0, the strict inequality a > (1 + epsilon)b ensures invertibility of
the leading overlap block. This allows the graph representation [I; F_0].
The residual implies the positive-semidefinite weighted inequality (5.3),
not merely a Frobenius or average-angle estimate. Both diagonal factors in
(5.4) are strictly positive. The contraction K has Frobenius norm squared at
most k regardless of the tail dimension.

The trace inequality (5.10) does not commute the head eigenvalue matrix with
F^T F. It shifts by a scalar a so that both comparison terms are positive
semidefinite. The scalar coefficient (5.11) is decreasing in the head
eigenvalue, and all tail eigenvalues, including negative ones and the endpoint
b, are covered. The polynomial has degree m-1, including its continuous
extension at u=1. The constant inequality for cosh(10) has an exact rational
certificate, not only a decimal numerical evaluation.

The unknown b is used only in an existence argument for a good subspace inside
the Krylov space. The algorithm does not require b. Processing m frontier
blocks costs at most km individual products, including the final compression.
Invariant-space and b=0 cases are explicitly covered. The objective for |M|
follows from the positive semidefinite difference |M|-M.

## 4. Transfer from the PCA lower bound

The hard distribution and its conditioning event are imported from [SAR18].
The stronger spectral event is a subset of the event defining that law and has
conditional probability at least 0.99 once the additional dimension condition
is imposed. The spectral approximation algorithm succeeds with probability at
least 0.99 for every fixed M. Consequently the composed PCA algorithm succeeds
with probability at least 0.9801 on the conditioned hard law.

The parameter is g=min(4 epsilon, 1/2), so epsilon <= g <= 4 epsilon. Positive
rank-k interlacing supplies the tail bound. The two accuracy intervals in
Section 6.2 both satisfy the postprocessor's gap assumption. All products with
M or M^T are the same oracle operation because the hard inputs are symmetric.

The lower bound first contains the subtraction of the postprocessing budget.
Absorbing that budget requires a universal lower threshold on log(n). All
polynomial dimension assumptions are retained. The report does not evaluate
or optimize their exponent D, and does not extend the conclusion to all finite
parameters by inserting an n-cap.

## 5. Padding transfer

The known block is L I_p with L larger than the residual threshold. This strict
inequality forces the top row block C of the returned basis to have full row
rank. The kernel of C extracts exactly the required lower-rank subspace.
The norm comparison yields no approximation-factor loss. An input query is
simulated by one query to the unknown block in the same oracle direction.

The application uses the bounded [BN23] hard family and the known value L=4.
It does not estimate or rescale an arbitrary unknown matrix norm for free.
On unsuccessful runs, an arbitrary valid output can be supplied if extraction
is undefined; only the success event is used in the reduction.

## 6. Completion and computational verification boundary

No all-adaptive lower-bound argument is supplied for the remaining joint finite
parameter regimes. The global k lower bound, the padded rank-one bound, and
the dimension-restricted growing-rank bound do not close every gap to the upper
bound. A complete solution to RA-14 is therefore not claimed.

The 18 unit tests, 270 block-Krylov trials, 60 warm-start trials, and 20 scalar
grids check finite computations. They neither establish the external random
matrix theorems nor verify all measurable adaptive algorithms. Some chosen
Krylov depths fail, and those failures remain in the supplied raw data.
