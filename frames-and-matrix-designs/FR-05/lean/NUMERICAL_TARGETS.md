# FR-05 theorem contract and current scope

The full target in `Challenge.lean` remains:

```text
∃ C > 0, ∀ d ≥ 2, phaseRetrievalProbability d ≤ C / d.
```

Here `phaseRetrievalProbability` uses the iid standard complex-Gaussian frame
law with `4d-5` rows and the original all-signal phase-retrieval predicate.
The injectivity event is now proved Borel measurable.
The exact quantitative target is now proved in `Solution.lean`, together with
the original limit $p_d \to 0$; see [FINAL_ASSEMBLY.md](FINAL_ASSEMBLY.md).

## Completed propositions

- [Proposition 3.1](PROPOSITION_3_1.md):
  `NLA.FR05.proposition_3_1` bounds the canonical planted injectivity
  probability by `C/M²` eventually.
  `NLA.FR05.proposition_3_1_haar` proves the same statement after Haar
  orientation. The construction supplies `C = 113`, a complete probability
  good event, and the local contraction proof.
- [Proposition 3.2](PROPOSITION_3_2.md):
  `NLA.FR05.proposition_3_2` proves `sourceLikelihoodL2 M ≤ C/M`
  eventually for the literal planted/reference likelihoods. Lemmas 3.3–3.5
  and all analytic prerequisites are proved.

No analytic assumptions or proof placeholders remain in these propositions.
The sharper intermediate exponents of Lemmas 3.6–3.7 are not claimed: a
conservative small-ball calibration suffices for Proposition 3.1.

## Completed final assembly

`NLA/FR05/Asymptotics.lean` proves that an eventual comparison

```text
p_d ≤ a/d² + sqrt(b p_d/d)
```

implies the full `C/d` theorem. `NLA/FR05/FinalAssembly.lean` now proves this comparison
for the original event using the planted/reference law identities, Propositions
3.1 and 3.2, and event-local Cauchy–Schwarz. Finite-prefix absorption gives a
single positive constant for every `d ≥ 2`; squeezing then gives the limit.
No mathematical proof obligation remains for these exported targets. The
separate independent review and isolated Linux verification remain outstanding,
so the problem catalog status is unchanged.

The scalar sampler is now identified exactly with the planted two-coordinate
density law, and the sampled column with that law plus an independent Gaussian
tail. The full-frame and Haar-mixture equality is also proved:
`NLA.FR05.source_haar_planted_frame_law_eq_likelihood` identifies the generative
Haar-planted frame law, after the canonical dimension relabelling, with
`standardComplexGaussianFrame (4*M-5) M` reweighted by
`ENNReal.ofReal (sourcePlantedLikelihood hM)`, for every `M ≥ 2`.

The corresponding reference-law identity is proved as
`NLA.FR05.source_reference_frame_law_eq_likelihood`. Its construction scales
the first two Gaussian coordinates by the positive square root of the reference
variance, then applies an independent Haar orientation. Both transformations
preserve injectivity. Thus `NLA.FR05.source_reference_injective_probability`
identifies its injectivity probability with the original Gaussian probability;
`NLA.FR05.source_reference_injective_integral` gives the equivalent identity
$\int_E L_r\,d\mu = p_M$. These statements use the original event, row count,
and Gaussian law, and hold for every `M ≥ 2`.

## Parameters

`N = 4M-5`, `n = M-2`, `η = 1/100`, `δ = M^-2`,
`ε = M^-50`, and `κ = M^-12`.
The completed contraction uses radius `R = M^-30` for `M ≥ 8192`.
