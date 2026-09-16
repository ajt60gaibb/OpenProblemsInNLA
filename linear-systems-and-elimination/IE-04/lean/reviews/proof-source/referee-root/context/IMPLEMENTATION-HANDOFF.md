# IE-04 complete proof candidate handoff

Original mathematical solution and formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI assistance is disclosed. The original
uniform-tail question remains attributed to Spielman and Teng. No George email
is included.

All 21 unchanged frozen Challenge declarations now have candidate implementations
in the private source tree. This statement is about source completeness, not
complete verification. `CANDIDATE-SOURCE-CHECKS.json` records literal signature
agreement after whitespace normalization, unique declaration names, all source
hashes, no implementation holes/axioms/native code and no Challenge import.
Actual final acceptance still requires the complete Linux build, measured
Comparator/default-kernel controls and two non-implementing final referees.

The immutable boundary and both independent approvals are bound by
`STATEMENT-FREEZE.json`. The Definitions and all 21 Challenge statements actually
elaborated in run 35021977948 at bdfbbddfd09c5ddde06c3eac6acb002022c234f1;
that combined run failed for other projects. Later actual run 35026411039
accepted the generic Pivot and GEPP implementations and all three new scalar
estimates with standard axioms. It also accepted Gaussian probability and
event-measurability declarations, but the Measurability module as a whole failed
on finite-supremum/function-elaboration details. Those and the self-row-swap
rewrite in StrictPivots have candidate repairs pending a fresh run. The
downstream witness, robustness, Gaussian-product, asymptotic and final modules
must not be described as mechanically accepted before their real logs arrive.

| Modules | Frozen targets and purpose |
|---|---|
| `Pivot`, `GEPP` | Existing IE-05 generic source, with full attribution, proves actual finite entry maxima, smallest-index maximal pivot selection and complete first-path semantics. No IE-05 numerical witness is imported. |
| `Measurability` | `firstPath_admissibleRule`, `gaussianMatrix_probability`, `exceedanceEvent_measurable`. The actual fold, selected Schur updates and finite maxima are measurable; the rule class is explicitly nonempty. |
| `Scalars` | `scalar_budgets`, `quotient_bounds`, `scalar_schur_error`. The exact closed-box radius and amplification leave a 1/8 error budget at every active stage. |
| `StrictPivots` | The necessary reverse active-block kernel argument proves original-matrix nonsingularity from actual nonzero pivots. Strict pivots imply admissibility and uniqueness of every full admissible path. |
| `Witness` | `witness_trajectory`, `witness_strict_growth`. Symbolic exact stages give actual determinant, strict pivoting, input maximum one and peak `(3/2)^(n-1)`. |
| `Robustness` | `full_box_robust`, `growth_on_box`. Induction covers every matrix in the closed box, every dimension and every admissible path, including final pivots and strict growth. |
| `GaussianDensity` | `standard_normal_density_lower`, `gaussian_interval_lower`. The only numerical certificate is `exp(-2)>1/8`, with kernel LeanCert at fixed Taylor depth 12. Analytic monotonicity and pi<4 cover the entire scalar interval. |
| `GaussianBox` | `gaussian_box_product`, `gaussian_box_probability`. The actual nested Gaussian rectangle has the exact product measure and the source exponent `n²(n²+n+5)`. |
| `ProbabilityTail` | `gaussian_box_in_actual_event`, `gepp_gaussian_tail_lower`. The original box enters the actual nonsingular high-growth event for every admissible rule at center I and noise scale one. |
| `Asymptotics` | `contradiction_dimension`. Exponential domination with arbitrary real exponents chooses a dimension for every positive real pair of tail constants; no large dimension is enumerated. |
| `Final` | `counterexample`, `not_uniformExponentialTail`. The identity's true spectral norm, exact threshold equality and strict dyadic probability comparison complete the original uniform negation. The final contradiction explicitly instantiates the verified firstPath rule. |
| `Solution` | The five generic `_proved` results receive their exact frozen names; the remaining 16 already have those names. All 21 receive LeanCert kernel assertions and printed axiom dependencies. |

Important final referee checks are the ordinary nested product measurable
space, the all-rule/nonempty-rule quantifiers, the reverse injectivity bridge,
the entire closed-box induction, the actual Gaussian event rather than an
uninterpreted certificate, the strict probability inequality, and the
arbitrary-real-constant asymptotic step. The final canonical publication
metadata must replace the old statement-only status with measured truth and
include exact accepted input hashes and logs. A failed combined development
run or a green selected/skipped job is not complete project acceptance.
