RE05 actual complement and spectral split
=========================================

The five new files contain 63 declarations in 594 lines. They concern the
existing actual query plan, complement, fold basis, and leverage matrix. They
do not change the model or claim the Gaussian success probability,
`OriginalClaim`, `SourceCompanion`, or the full RE05 `Target`. They make no
Linux, Comparator, canonical-package, or promotion claim.

`ComplementProjection.lean` forms a rectangular frame from exactly the
model's `uColumn plan h` lookups. `selectedProjection` is that frame times
its transpose, and `residualProjection` is the identity minus that matrix.
The model's actual `complement plan x` equals the latter matrix applied to
`x`; its self-adjointness is proved as the literal real dot-product identity.
For every actual `makePlan`, the selected list is the literal filter of
`finRange` and is duplicate-free. The actual SVD's full column orthogonality
therefore gives the frame Gram identity without an orthonormality promise.
The two actual row projectors are idempotent, multiply to zero in both
orders, and sum to the identity. Generic conditional matrix lemmas are
supporting algebra; the actual-plan endpoints discharge their hypotheses.

`PositiveSVDColumns.lean` extracts further consequences of every literal
PSD SVD. The previously proved weighted column inner-product identity and
unit norms force equality of left and right columns at positive singular
values. The weighted-entry identity also holds at zero, without forcing
those arbitrary full bases to agree. Thus the original matrix diagonalizes
in precisely the actual supplied full U, with no replacement eigenbasis.

`LeverageMask.lean` proves equality of the actual selected lookup sum and
the exact strict-threshold diagonal mask in that same U. Both selected and
residual row projectors are identified with their masks. Equality at the
threshold remains in the residual block. Full U's Gram and co-Gram
identities are proved from the literal SVD relation, including empty
dimensions.

`ResidualLeverage.lean` diagonalizes the actual residual leverage as
`H * leverage P * H`, whose diagonal values are zero at selected directions
and the actual singular value otherwise. Every such value is at most the
exact threshold. Conjugating the corresponding nonnegative diagonal
difference proves the literal PSD/Loewner upper bound

    threshold * I - H * leverage P * H >= 0.

The exact quadratic inequality is proved for the actual model complement.
These endpoints require no independence or positive-accuracy promise: the
model's square-root threshold is always nonnegative. In particular they
apply at the required positive accuracy, and also cover total-model
exceptional inputs. The actual residual basis blocks are `H * E_j`, where
`E_j` is exactly `orthonormalMember P j`. Their Gram-product sum is proved to
be `H * leverage P * H`, and the selected plus residual blocks reconstruct
every actual basis matrix.

`BasisProjection.lean` proves the literal entrywise Frobenius inner product
is the transpose-product trace. Orthogonality of the two row projectors
gives exact Frobenius splitting. Under only the original `Independent P`,
the accepted actual fold orthonormality then gives each actual residual
basis block norm at most one. It also defines the selected and residual
coefficient Gram matrices from these exact basis blocks. Both are PSD,
their actual-plan sum is the literal coefficient-space identity, and both
are bounded above by that identity. Thus `K+H=I` is available both for the
row projectors and for the normalized-basis coefficient Gram blocks. These
are deterministic analysis identities, not a probability or postprocessing
correctness assertion about the original supplied-coefficient solve.

All 18 original/model/review/registry/pin inputs and every frozen
prerequisite remain exact. No original, permanent ID, canonical README,
Target, model, status, or catalog was edited. The source freeze also checks
the earlier attained/SVD, actual orthonormal-fold, spectral-charge,
orthogonal-optimum, query-count, and asymptotic sources for preservation.

All five producers and the first literal development consumer passed in
LeanCert kernel mode with only the standard three axioms or a subset. All
63 authored declarations are explicitly kernel-asserted in that consumer,
with 15 additional actual-model/edge/interface assertions. The consumer
checks actual `plans P epsilon omega copy`, actual complement, matrix and
quadratic residual bounds, raw block Gram sum, both row/coefficient
identity splits, coefficient PSD bounds, Frobenius splitting, and residual
block norm. It includes a dependent zero family and an empty-dimensional
complement; the reviewed full-target identity is an identity check only.
Development source-elaboration logs are retained; those checks reuse
private development objects and are not fresh evidence.

The separate fresh replay begins with no private project output objects,
snapshots every local producer, and checks the same 78-assertion consumer.
A separate unresolved-False control must fail at kernel trust with
`sorryAx`. `final/result.json` records the terminal result and exact raw
commands/log hashes. This document is author analysis and makes no
independent source-review claim.
