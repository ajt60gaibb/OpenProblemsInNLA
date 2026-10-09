# MF-17 statement correspondence

The original target is retained in `../README.md`. The manuscript source is
Part VI, Theorem S.1.1 (printed page 42) of `../MF-17-research-handoff.pdf`.

For every real M > 1, the growth envelope over all complete complex Hilbert
spaces and strongly continuous semigroups satisfying ||T(s)|| <= M exp(-s)
for every s >= 0 has matching positive upper and lower bounds of order
(log log(t + exp(exp(1))))^((2/pi) arccos(1/M)) for every sufficiently large
t. The constants depend only on M; the Hilbert space, generator, and time
are quantified after the constants. The threshold is positive.

`ProofProject/Definitions.lean` defines `StableSemigroup`, the full strong
right-derivative `GeneratorGraph`, the bounded everywhere-defined inverse
relation `IsGeneratorInverse`, and the norm-convergent operator exponential
`inverseEvolution`. The graph uses all x,y satisfying the derivative condition;
it is not an arbitrary restriction of the generator domain. Negative semigroup
times are unused. No separability or finite-dimensionality is assumed for the
upper bound. A fixed arbitrary Lean universe is used for the class of spaces.

`growthLog` uses natural logarithms; `growthExponent` is exactly
(2 / pi) * arccos(1 / M). `attainableNorms` quantifies over the spaces,
semigroups and inverses, and `growthEnvelope` is its real supremum.

The independent `Challenge.lean` contains five targets:

- `ProofProject.stableSemigroup_hasGeneratorInverse`: unique bounded inverse
  for each stable semigroup, including M = 1.
- `ProofProject.attainableNorms_bddAbove`: boundedness of the supremum's
  defining set at every t >= 0 and M >= 1.
- `ProofProject.sharp_growth`: the original matching fixed-M asymptotic.
- `ProofProject.finite_dimensional_lower`: finite-dimensional lower witnesses
  with the exact same M. The witnesses may depend on t.
- `ProofProject.contractive_envelope`: the exact endpoint G_1(t) = 1 for
  every t >= 0, including t = 0.

The zero Hilbert space is allowed and does not change the envelope. No
uniformity as M decreases to one, limit of the normalized envelope, optimal
leading coefficient, numerical tail constant, or manuscript Part IX claim
is included in these targets.

The proof is symbolic. No numerical certificates or unverified numerical
inputs enter the target declarations. The solution modules may replace
manuscript arguments with other proofs of the same statements. This submission
imports an existing formalization; the reviews recorded here are retrospective
and are not described as preceding its implementation.


## Adaptations of the manuscript proof

The formalization proves the target of Part VI, Theorem S.1.1, using an
adapted scalar lower construction. It is not a literal transcription of
all the intermediate constructions or constants in that part.

`SourceWeightFactor.sourceWeightFactor` uses the symmetrized scalar factor

```text
ψ(z) = ((1+z)/(1-z))^(α/2)
       exp((α/4)((1-z)^ν - (1+z)^ν)),  ν=(1-α)/2.
```

The manuscript's (S.7.2) instead displays
`h(z) = (1-z)^(-α/2) exp((α/4)((1-z)^ν - 1))` and then uses a
two-component matrix factor in (S.7.6). The Lean proof uses scalar weighted
monomials, an alternating-sign coefficient witness, orthogonal replication,
and a separate Euclidean metric perturbation. Its dimension is `r*n`, with
an inverse-square metric margin and separation parameter `n^3`; the
manuscript's (S.8.1) uses `2*r*n` and a different margin. The formalized scalar
factor has its own principal-branch and boundary estimates. This submission
does not use an unproved identification with `h(z)/h(-z)` to justify them.

The coefficient-deficit constant `(M^4+1)/(M^2-1)` in
`CoefficientSquare.coefficientDeficit_interior_lower` is a proved refinement
of the manuscript's `2*M^4/(M^2-1)` in (S.6.6). Similarly, the Lean endpoint
surplus `1/(4B)` in `HasBoundaryEstimate.replicationDeficits` refines the
`1/(8B)` in (S.6.4). The formal proof establishes these constants directly;
none is assumed from the manuscript.

Accordingly, inherited comments calling these formulas or constants
“exactly” those of “the source” in `SourceWeightFactor.lean`,
`SourceDirichletGain.lean`, and `CoefficientSquare.lean` refer to the adapted
construction and should not be read as literal attributions to equations
(S.7.2) or (S.6.6). This correspondence note explicitly corrects those
attributions while retaining the reviewed proof-source bytes. No change to
the target, executable Lean code, or manuscript is made.
