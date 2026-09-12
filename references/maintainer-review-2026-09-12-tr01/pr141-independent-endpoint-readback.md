# PR141 independent endpoint client: read-only semantic check

Client reviewed: `/private/tmp/nla-review-tensors/pr141-independent-endpoint.lean`.
Proof source inspected: immutable external commit
`ed21181197ac839eac95f549404f94e7e3aa6e10`.

Verdict: **PASS for literal canonical-target correspondence.** This readback
does not claim that the client compiled; the independent Lean reviewer owns
its compilation, dependency, and axiom checks.

- `reviewer_prescribed_squared_norm_success` uses
  `certified_explicit_main.2`, with `k=prescribedWidth m r ε` definitionally equal
  to `min (2^m) (Nat.ceil (C*r/ε^2))` at the manuscript's explicit constant.
  `frameFailureProbability_le_sup` supplies the fixed-frame bound at that exact
  same width. No existential/selected-width endpoint theorem is invoked.
- The displayed conclusion places `∀ x` inside the probability event. It is a
  simultaneous squared-norm guarantee for every vector of this fixed frame's
  image, not separate 0.99 guarantees for each vector.
- `V` and its hypothesis `V.transpose * V = 1` are outside the probability.
  Every fixed r-dimensional real Euclidean subspace has a deterministic
  orthonormal basis of this form, and the image of such a matrix consists of
  exactly the vectors `V.mulVec x` with `x : Fin r → ℝ`. Thus the frame statement
  gives the canonical arbitrary-fixed-subspace statement. The claim is not a
  simultaneous event for all subspaces, which the canonical target does not
  require.
- `uniformProbability` is normalized counting on the complete product of two
  Boolean sign-function spaces and the subtype of subsets with exactly k
  elements. It therefore describes independent Rademacher entries in both
  layers and an independent uniform sample without replacement. The primitive
  matrix `rerandomizedSRHT` has exactly the required normalization and order
  `sqrt(n/k) D1 H D2 H S`.
- `squared_edges_iff_spectral_bound` is a pointwise equivalence between the
  literal simultaneous squared-norm inequalities and the operator norm of
  `Vᵀ Ω Ωᵀ V−I` being at most ε. Its use here does not invoke the earlier
  selected-width probability theorem, although it resides in the V6 module.
- The complement step is valid: the failure event is strict `norm > ε`, and
  its complement is the inclusive two-edge success event. Nonemptiness of the
  finite sample space is supplied through `k≤n`. The failure bound `≤1/100`
  becomes success `≥99/100`.
- `walshCard m = 2^m` includes m=0/n=1. The source covers all `1≤r≤n` and
  `0<ε<1`, hence the canonical `0<ε<1/2`. The witness's positivity can be paired
  with `certified_explicit_main.1`; no V-dependent constant occurs.

Definitions checked in `Definitions.lean`, `PaperV7/ExactWidth.lean`,
`PaperV7/Expected.lean`, and `PaperV7/Certification.lean`; pointwise conversion,
supremum domination, and finite-complement facts checked in
`PaperV6/FixedFrame.lean` and `PaperV6/FixedFrameExpected.lean`.
