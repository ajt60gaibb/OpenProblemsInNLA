# RA-10 completion checklist

Checked boxes mean a local Lean proof exists, not that independent review or
the required isolated Linux verification has been completed. The unchanged
`NLA.Statements.RA10.Target` is now proved locally with witness 11 in
`OperatorMonotoneRepresentation.lean`. Mathematical proof development is complete;
independent review and isolated Linux verification remain outstanding.

Before implementing each section, inspect existing RA-10 modules, the pinned
Mathlib and relevant external work; record useful reuse and simplifications.
Do not replace the full target by a special case or an additional hypothesis.

## 1. Spectral and nuclear-norm foundations

- [x] Frozen PSD/spectral definitions and their Mathlib bridges.
- [x] Nuclear norm: positivity, zero criterion, triangle inequality, homogeneity,
  orthogonal invariance, ideal bounds, PSD trace and positive-part identities.
- [x] Selected projections, compression spectra, tail identities and eigenvalue comparison.
- [x] Sharp ordered-eigenvalue nuclear perturbation inequality.

Reuse: existing RA-10 proof modules and Mathlib's finite-dimensional spectral
theorem. The common upper bound `Y + (X − Y)₊` gives the perturbation bound
without a separate general eigenvalue-perturbation library.

## 2. Ridge compression lemma — locally complete

- [x] Ridge resolvent formulas and invertibility of positive shifts.
- [x] Derive the two block-energy equations from an actual positive ridge eigenvector.
- [x] Derive the selected-component mass bound from those equations, including singular compression.
- [x] Prove the positive-eigenvector inequality, source (6)–(7).
- [x] Sum the positive-eigenvalue bounds using positive-part trace bounds.
- [x] Export the full compression lemma for arbitrary PSD matrices and orthogonal projections.

Reuse: `RidgeResolventProduct`, `RidgeCompressionMass`,
`HermitianPositivePartOrder`, and Mathlib's Hermitian eigenbasis. The existing
projection/trace arguments in `MatchedLeadingEq11Variational` were inspected;
the implementation instead uses the shorter full-basis argument below.
Simplifications implemented: positivity tested at `μu + w` replaces the
inverse-based Schur-complement step; the equations are derived for singular
compression directly, removing regularisation and limits. The pointwise bound
uses `(C − A)₊ + (cP − C)₊`, so summing over a full eigenbasis replaces the
positive-eigenspace variational argument. See `RidgeCompressionEnergy`,
`RidgeCompressionQuadratic`, `PositivePartTraceBound`, and `RidgeCompression`.

## 3. Complete ridge transfer

- [x] Matched-spectrum estimates, source (8)–(14).
- [x] Actual selected-approximant estimates, source (16)–(18).
- [x] Constant-11 assembly conditional on the compression estimate.
- [x] Zero-tail ridge case, with no compression hypothesis.
- [x] Discharge the compression hypothesis and export unconditional ridge transfer.

Reuse: `RidgeTransferConditional` already assembles these results using the
frozen nuclear norms and the supplied eigenvectors, including ties and zeros.
`RidgeTransfer.lean` exports `NLA.Proofs.RA10.ridgeTransfer_eleven`, with no compression, representation,
invertibility, commutation, gap, or positive-tail premise.

## 4. General operator-monotone representation

- [x] Recheck available formal libraries for the full positive Löwner representation.
- [x] Derive scalar monotonicity and concavity from the frozen real-matrix hypothesis.
- [x] Prove the growth bounds, normalize at one, and discharge the identically zero case.
- [x] Define the compact harmonic kernel, retaining constant and linear endpoints;
  prove nonnegativity, uniform domination and integrability for every finite measure.
- [x] Extend a representation on strictly positive arguments to zero by dominated convergence.
- [x] Construct a probability measure for every profile in the closed convex hull
  of the harmonic atoms, including pointwise limits of finite convex combinations.
- [x] Build the compact convex class of normalized positive profiles and apply
  Mathlib's Krein–Milman theorem to it.
- [x] Prove that its closure preserves normalization, strict positivity, scalar
  concavity, continuity on `(0,∞)` and all-size real matrix monotonicity.
- [x] Identify that compact class intrinsically: normalized positive shifts
  approximate every continuous positive operator-monotone function on `(0,∞)`.
- [x] Prove all harmonic atoms belong to the frozen admissible class, using
  real matrix inverse-order reversal and the checked ridge resolvent identity.
- [x] Prove that the constant and linear endpoint atoms are extreme.
- [x] Prove the harmonic formula for an extreme profile **given a nonnegative
  operator-monotone Hansen split**, including zero-weight endpoint cases.
- [x] Define the two canonical divided-difference pieces and prove their
  nonnegativity, sum and splitting identity.
- [x] Prove independence of the supplied spectral basis and bridge to Mathlib's
  functional calculus, including reindexing, orthogonal conjugation and block sums.
- [x] Prove the block compression inequality and all-size matrix concavity on
  strictly positive matrices from operator monotonicity and continuity.
- [x] Prove differentiability at every positive argument by a two-by-two
  comparison and Mathlib's one-sided derivatives of convex functions.
- [x] Discharge the differentiability premise in the Hansen split: both
  canonical pieces are now proved continuous on `(0,∞)`.
- [x] Prove the finite-matrix divided-difference derivative without differentiating eigenvectors.
- [x] Prove the Kraus second divided-difference sign by an arrowhead compression.
- [x] Prove the matrix monotonicity criterion, including finite spectral crossings
  of the anchor and removal of the auxiliary invertibility condition.
- [x] Prove Bendat–Sherman and matrix monotonicity of both Hansen pieces.
- [x] Classify the compact class's extreme points as harmonic atoms.
- [x] Prove measure existence for normalized positive profiles and all admissible functions.
- [x] Discharge the representation-existence premise of the transfer theorem.

The reuse search found only special-function integral representations in
pinned Mathlib and the external work checked. The implementation now reuses
Mathlib's Krein–Milman theorem, compactness of probability measures on compact
spaces, closedness of scalar concavity, finite-sum integration and dominated convergence. See
[`REPRESENTATION_PROGRESS.md`](REPRESENTATION_PROGRESS.md) for the reuse audit
and the final unconditional signatures. The compact finite-measure formulation
lets the transfer proof avoid a separate weighted infinite-measure conversion.
Further reuse: Mathlib's Schur complement (`Matrix.PosDef.fromBlocks₁₁`)
gives an exact block comparison without matrix norm estimates. Its convex
one-sided derivative API and a fixed two-dimensional comparison prove
regularity without assuming the divided-difference theorem.
The final analytic step reuses Mathlib's continuity of CFC in the matrix,
Schur's Hadamard-product positivity theorem, the mean-value theorem and
finiteness of polynomial roots. An exact column identity replaces a general
Fréchet derivative library; arrowhead compression replaces a general second
derivative theory. Applying Bendat–Sherman to `-f(1/x)` supplies the other
Hansen piece without a separate operator-perspective or involution theorem.

## 5. Transfer from represented functions — locally complete

These checks concern functions given a representing measure; section 4 now
establishes its existence for every admissible function.

- [x] Constant and linear atoms, preserving the selected projection when `f(0) > 0`.
- [x] Entrywise/spectral integration and absolute convergence.
- [x] Nuclear-norm integral inequality and the exact optimal-tail identity.
- [x] General represented-function transfer, including zero tail and selected zero eigenvalues.

Reuse implemented: Mathlib's Bochner finite-sum and dominated-convergence
theorems, existing spectral tail formulas, and the earlier nuclear trace-duality
proof. Trace duality supplies the integral inequality without a new matrix norm
instance. The atom theorem already covers zero tail, so the integral proof
handles it without a separate limiting argument.

## 6. Final theorem and verification

- [x] Prove `TransferBound 11` and witness the unchanged `Target`.
- [x] Record final signatures, source hashes and the local build log.
- [x] Audit all transitive axioms of the representation, transfer bound and frozen target.
- [ ] Obtain independent scope and proof reviews of the final source hashes.
- [ ] Run isolated non-root Linux Comparator with controls.
- [ ] Only after verification, update the retained canonical page and status, preserving all IDs.

Local check:
`lake build NLA.Proofs.RA10.OperatorMonotoneRepresentation NLA.Proofs.RA10.OperatorMonotoneConcavity`.
The unconditional representation, `transferBound_eleven` and `ra10_target`
report only `propext`, `Classical.choice`, and `Quot.sound`. The statement hash
is unchanged. Evidence is in `verification/2026-10-11-complete/`.
Independent review and authoritative Linux verification remain open; no
Docker or Podman executable was available in this macOS session.

Original development branch: `codex/ra10-spectral-transfer`, at baseline
`50106db1b75a1019b708f495db747ab37bb8efbd`. The upstream submission branch is
`codex/ra10-complete-upstream`, based on PR #350 at
`696b59ff414c74d24bfef71ab22e6d67b5c0f7cd`; its local check is retained in
`verification/2026-10-11-upstream-pr/`. See
[`SPECTRAL_TRANSFER_PROGRESS.md`](SPECTRAL_TRANSFER_PROGRESS.md) for earlier
local checks and their limits.
