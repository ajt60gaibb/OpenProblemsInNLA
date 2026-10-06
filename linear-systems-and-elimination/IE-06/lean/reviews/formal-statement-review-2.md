# IE-06 independent formal statement review 2

Review date: 2026-10-06. Reviewer: infrastructure agent, independently assigned
to the mathematical implementation after its completion. I authored the local
infrastructure and test drivers, but did not author or modify the mathematical
files reviewed here. This is an AI-agent review, not human peer review or an
endorsement by John Urschel. My execution of the infrastructure is not claimed
as an independent review of my own test-driver implementation; a different
agent reviews that boundary.

**Disposition: accepted as a faithful statement package, with the explicitly
conditional and semantic supporting proofs described below. No unconditional
Lean proof of IE-06 or of the source tail is accepted or claimed.**

## Reviewed source bytes

Paths below are relative to this Lean project.

| File | SHA-256 |
| --- | --- |
| `NLA/IE06/Definitions.lean` | `a5a8bf8d4a9f6dc97d0b645a4ed7639ee808ae4d340dc70c913e06ed5057c19a` |
| `NLA/IE06/Statements.lean` | `4bdb38cf65e1ab8859efd45946a7de346f1a3ed93454be926fc0b4406a735c7b` |
| `NLA/IE06/Semantics.lean` | `c61cd8770a62e844e678f738ef98f5de5521d8d23dcd0560f34744029d30e112` |
| `NLA/IE06/Reduction.lean` | `0e2faeb5cecf638e1312f08adc777f13b32af3a348fa737c600f96ff644516ad` |
| `NLA.lean` | `02493f578226d478d3b9fd743a59560343c50cea819b7e282abcffee3dd795e2` |
| `Challenge.lean` | `701de729aceba6a69c72440c030b98c686942571b7f0160c84bdd9b95ceecbda` |
| `comparator.json` | `de4f4300a69054519964694f6228084cd063e843b3a29ec1815348ac493f4d6a` |
| `reviews/statement-specification.md` | `c58ae67bbbd2d9764c75924eec6a400e23d65e90ccbc2257ead8db01ec24592b` |
| `NUMERICAL_TARGETS.md` | `2167d6232b81565d7af68a0efcb74b2521153708751a5d19f2e88bdee7fdcab4` |
| `source/original-HEAD-README.md` | `60a6d3ba647c4443e07e906cca8950007c15c12e326c8496db8a670e6ec308bf` |
| `source/working-README.md` | `15b987cd776e9a4483fd9b8dabd15c945ac5fe4898b7231c6b2f3269a731d523` |

I compared the full canonical working README and both retained README copies.
The canonical working README has SHA-256
`15b987cd776e9a4483fd9b8dabd15c945ac5fe4898b7231c6b2f3269a731d523`, matching
the initial task inventory. The TeX and PDF still match their initial hashes
`b73d3f78fdbce9badb64eae1193eb8813b39ef27841426b6b4688b5e9e90a5b5` and
`dc97a3d6c063848893e23e360af918357c7952375f9ad62424e9be49c3ef1668`.
The original permanent ID and complete original target remain intact.

I independently opened the versioned primary manuscript, including Theorem 1.4
and Section 5.1. The displayed theorem uses LU growth, while Section 5.1
explicitly explains the stronger control of every active Schur-complement
entry. The fixed pivot rule has a Gaussian-null tie exception. Accordingly,
the package correctly labels the all-path all-Schur rate as an extraction from
the argument, not a literal copy of the LU theorem. Normalization and the null
exceptional-set bridges remain unformalized. This is a correspondence check,
not a full audit of the manuscript's proof.
[Source: Urschel, arXiv:2610.06785v1](https://arxiv.org/html/2610.06785v1).

## Concrete mathematical fidelity

`Mat n` is the full real square-matrix space indexed by `Fin n`. The nested
finite product `gaussianReal 0 1` specifies exactly n² mutually independent
standard real Gaussian entries. I checked the pinned Mathlib definitions:
`gaussianReal` takes mean and variance, and `Measure.pi` is the finite product
measure. No arbitrary probability function, deterministic center, truncated
law, conditional sampling, or unspecified growth oracle is introduced.

`rowSwap` changes current row positions only. `schurStep` uses the exact
rank-one Schur formula and zeros the already eliminated rows and columns.
`AdmissiblePivot` requires the pivot row to be active, the pivot to be nonzero,
and every active first-column absolute value to be no larger. Equality is
allowed. Thus every tie choice is retained, rather than a favorable selected
path. `trajectory` applies one such elimination per stage.

The numerator of `growth` maximizes actual absolute entries over active rows
and columns at every stage indexed by `Fin n`: the input and final scalar
complement are both included. It does not include stored multipliers, nor
restrict growth to the pivot or U entries. Measuring the maximum immediately
before the next row swap is faithful because the swap only permutes active
rows. The denominator is the original maximum absolute input entry. Total
division on invalid inputs does not enter the probability event: that event
requires positive dimension, nonsingularity, and an admissible path.

The existential bad path in `exceedanceEvent` is the correct negation of a
bound holding for every admissible path. The threshold is strictly exceeded.
The dimension-zero event is explicitly empty. Singular inputs are excluded
without conditioning the Gaussian measure; their nullity is separately exposed
as a proof obligation. Event measurability and nonsingular admissible-path
existence are also explicit obligations, not added hypotheses that silently
make the main target easier. Until measurability is proved, applying the Lean
measure uses its standard all-set extension; the exact finite rational event
remains concrete and its Borel-measurability contract is retained.

`SquareRootUpperBound` quantifies over every positive real η and takes the
limit over all natural dimensions. Its exponent is the exact real rational
1/2 plus η. The convergence is in nonnegative extended reals, with no lossy
conversion of infinite measure to zero. The Gaussian normalization helper
proves that the concrete product law is a probability measure. The stronger
rate has the reviewed quantifier order: for every positive α, a positive C
and natural cutoff N ≥ 2 work for every n ≥ N; they cannot depend on the
sampled matrix, pivot path, or later dimension. Neither statement introduces
an unsupported lower bound, finite dimension restriction, or distributional
claim.

## Supporting proof and challenge scope

The four `Semantics` proofs have their advertised limited meanings:
probability normalization, empty zero-dimensional event, antitone threshold
events, and unit growth of a nonzero one-dimensional matrix. The analytic
threshold proof in `Reduction` has all necessary sign and domain conditions:
C ≥ 0, η > 0, x ≥ 1, and log x ≥ (C/η)². Its square-root and exponential
monotonicity calculation proves exactly the stated threshold comparison.

The conditional limit proof selects tail exponent α = 1, uses eventual
threshold domination and monotonicity of measure, and sandwiches the event
measure between zero and `ofReal(n^(-1))`. The latter tends to zero. The
hypothesis `SchurSubpolynomialTail` remains explicit in the final theorem;
it is not introduced as an axiom or misreported as a proved random-matrix
result. No numerical search or finite sample is used to justify asymptotics.

`Challenge.lean` contains six isolated reference theorem signatures with
intentional `sorry` placeholders. Neither `NLA.lean` nor any concrete module
imports Challenge. The future Comparator configuration lists the original
unconditional theorem, the additional tail, and semantic obligations, with
no definition holes and only the three foundational permitted axioms.
It cannot turn these placeholders into accepted solutions; `Solution.lean`
is intentionally absent. The scalar LeanCert fixture is separated from the
IE-06 theorem claims.

## Actual checks observed

The final full local source-snapshot run is
`verification/local/attempt-bpcivixz/result.json`, SHA-256
`cdef517e6a7d895e22bbc68533e96146719c6cd9b64077b78a3a74f4931506c0`.
It successfully compiles Definitions, Statements, Semantics, Reduction, the
NLA umbrella, Challenge, and the separate numerical control. Its audit reports
that all 42 concrete local declarations have only permitted transitive axioms.
The sorry/native negative controls are rejected as intended. All recorded
input hashes still equal the reviewed live bytes. The Challenge warnings are
expected and are not proof acceptance.

The local source check trusts the pinned compiled dependency cache. It is not
authoritative Linux sandbox/exporter/raw-kernel-replay verification. The nine
actual Comparator-core fixture assertions likewise test checker behavior,
not an IE-06 solution. These limits are consistent with the package's declared
statement-only scope. No mathematical correction was required by this second
implementation review.
