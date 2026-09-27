# Proposition 3.1

Import `NLA.FR05.Proposition31` for the canonical planted law, or
`NLA.FR05.Planted.PlantedHaarFailure` for its Haar orientation:

```lean
NLA.FR05.proposition_3_1
NLA.FR05.proposition_3_1_haar
```

Both prove an eventual `C / M^2` bound for the probability of the original
all-signal `PhaseRetrievalInjective` predicate under the actual generative
planted law. The proof supplies `C = 113`. It assumes no analytic estimates.

## Proof

- `SmallBall/RowDistanceProbability` makes the near-span event open. Product sections
  permit choosing a unit normal separately for each fixed collection of other
  rows; no measurable normal selector is needed.
- `Planted/SourceRowDistance` applies the existing source-law small-ball estimates and
  the deterministic least-gain inclusion, then takes the finite union bound.
- `SmallBall/SourceRowSmallBall` chooses `t = M^-6` at `κ = M^-12`. This yields
  `P(least gain < κ) ≤ 112/M² + 100 M exp(-4M)`.
  The sharper intermediate exponents of Lemmas 3.6–3.7 are unnecessary.
- `Planted/SourceHighProbability` combines this with the row-energy event and the
  almost-sure source support. The complete good event fails with probability
  at most `113/M²` eventually.
- `Planted/SourceLocalControl` proves a finite-difference bound for the exact
  polynomial factor chart. Expanding symmetrically about the midpoint cancels
  the quadratic remainders and gives nonlinear constant `1024 M^6 R`.
  On a ball of radius `R`, the retained bound for the error relative to
  the frozen Jacobian has Lipschitz constant at most
  `512/M^44 + 2048 M^6 R`; the initial residual is at most `2/M^49`.
- `Planted/Newton` sets `R = M^-30`. For `M ≥ 8192`, the residual and
  Lipschitz bounds imply that the Newton map contracts by at most `1/2` and
  preserves its closed ball; the same module proves the fixed-point step.
- `Proposition31` turns that root into an exact phase-retrieval ambiguity.
  `Geometry/InjectivityMeasurable` proves the original injectivity event Borel
  measurable, so the probability transfer to the planted frame law is exact.
- `Planted/PlantedHaarFailure` proves right-unitary invariance of injectivity and
  equality of the canonical and Haar-oriented injectivity probabilities.

The row law, parameters, matrix, chart, and Newton hypotheses are all concrete.
The fixed-point proof uses the frozen Jacobian directly, so no separate
inverse for the perturbed Jacobian is required.

## Scope and verification

Proposition 3.2 remains proved separately in `LikelihoodComparison`.
The unconditional FR-05 Gaussian `C/d` theorem is now assembled in
`FinalAssembly`: the generative law bounds are connected to the likelihood-weighted
event comparison and the reference law. See [FINAL_ASSEMBLY.md](FINAL_ASSEMBLY.md)
for the completed proof and current local verification scope.

See [verification/proposition31](verification/proposition31/README.md) for the
historical component checks, and [the current audit](verification/library-cleanup/README.md)
for the current layout's complete build and axiom checks.
