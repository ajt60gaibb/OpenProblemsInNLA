# Independent preimplementation review: Gaussian smoothing

Reviewer: infrastructure/Gaussian agent, independent of root author. Verdict: APPROVED before implementation. Specification SHA-256 `ac352112c3d9421a94bb1ef2036ca6af1d2a6d718666636e991d1a0fbf7f3b23` at review time. This is a mathematical specification review, not a claim that subsequent code has been reviewed or compiled.

The fixed row-vector product X_i G is represented as the transpose of a Gaussian s by n matrix times the deterministic n by 1 column X_iᵀ. Its squared Frobenius and operator norms both equal the squared Euclidean row norm. The proved centered Frobenius tail therefore gives exactly (2s+4x) times this squared norm, bounded by (2s+4x)ζ², with no dimensional loss. ζ=0 is valid.

For QᵀQ=I, the actual compression QᵀG has the exact q by s iid Gaussian law. The approved and proved A2' applies because q≤r, r>0, s≥3r, giving squared pseudoinverse bound (3/r) exp(2+x/r). The q=0 case has the unique empty inverse and vacuous row-rank identity, consistent with both the deterministic cancellation and probability bound.

The good Gaussian events depend only on XG and QᵀG. Their intersection, along with the almost-sure full row rank of QᵀG, implies the asserted bound for every J satisfying the algebraic and row-l1 premises simultaneously. Thus a random J may depend arbitrarily on G; no independence or measurable choice of J is assumed. For an arbitrary actual bad set, outer-measure domination suffices. The n row events plus one inverse event give exactly (n+1)exp(-x), with no missing exceptional probability.
