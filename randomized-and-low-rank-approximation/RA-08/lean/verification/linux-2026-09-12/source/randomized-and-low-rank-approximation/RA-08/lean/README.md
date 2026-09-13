# RA-08: an exact concave spectral-transfer counterexample

**The complete fourteen-export proof has two accepted independent final mathematical approvals. Actual Linux verification is pending.** The [canonical problem](../README.md) remains **Solved**. This candidate documentation does not promote its verification status.

Formalization: **George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA**, with AI assistance. **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge, retains mathematical authorship of *Concave matrix-function error transfer can fail for exact Nyström approximations*. Persson, Meyer and Musco retain the original question's attribution. The new formalization has an Apache 2.0 license; it does not relicense the source manuscript.

## Complete target and counterexample

[Definitions](NLA/RA08/Definitions.lean) retains the complete original universal spectral-transfer implication: every real symmetric PSD pair `Ahat ≤ A`, every original dimension and rank, every nonnegative error parameter, every continuous nonnegative nondecreasing concave function on the nonnegative half-line, and every permitted ordered orthonormal eigendecomposition. The same selected eigenvectors are used for each matrix's two truncations. Generic admissibility allows `f(0) > 0`; the discarded function coefficients are zero.

The operator norm is the actual norm of `Matrix.toEuclideanCLM` on real Euclidean space. Function application is genuine Mathlib `cfc`. Existence of ordered spectral data, their CFC interpretation, extension independence and exact tail norms are proved for arbitrary selected decompositions, including repeated eigenvalues.

The unchanged source witness has dimension six, rank three and

```
t = 1/65536, a = 17/16, b = 127/128,
Ahat = diag(1/2, b, a, 0, 0, 0),
A = Ahat + t F,        f(x) = min(x,1),
```

where `F` is the exact rational rank-three projection defined in the source and in Definitions. The proof establishes actual positive definiteness of `A`, PSD order, exact residual norm `t`, and the fourth eigenvalue `t` for every selected ordered basis of `A`. Both optimal tails are `t`. The transformed error is strictly greater than `t`, refuting the full original implication at error parameter zero.

[Solution](Solution.lean) has exactly the fourteen frozen [Challenge](Challenge.lean) signatures:

| Export | Proved contract |
| --- | --- |
| `orderedSpectral_exists` | Every real PSD matrix has actual complete ordered orthogonal spectral data. |
| `orderedSpectral_semantics` | Selected columns are actual orthonormal eigenvectors and their spectral combination reconstructs the matrix. |
| `functionalCalculus_spectral` | Actual CFC equals the selected spectral combination; changing the scalar extension outside the half-line has no effect. |
| `spectral_tail_norms` | Both genuine operator-norm truncation tails equal their first discarded scalar coefficient for every selected basis. |
| `operator_rayleigh_bound` | The absolute quadratic form is bounded by the actual Euclidean operator norm times the squared vector norm. |
| `witness_data` | The unchanged function and matrices satisfy the full admissibility, projection, positive-definiteness and PSD-order properties. |
| `witness_spectral_location` | The actual witness spectrum lies in `[0,1] ∪ [17/16,∞)`. |
| `minorant_scalar` | The degree-six polynomial minorant is below `min(x,1)` on this entire unbounded spectral set. |
| `minorant_functional_calculus` | Genuine polynomial CFC and actual PSD order transfer that scalar bound to the fixed witness. |
| `witness_tail_data` | Exact residual, fourth eigenvalue and both truncation/tail identities hold for every allowed witness basis. |
| `witness_rational_certificate` | Actual matrix-vector, squared-length, CFC and Rayleigh identities give the exact rational strict-gap expression. |
| `numerical_gap_positive` | The materially used exact rational gap is positive by explicit-kernel LeanCert. |
| `counterexample` | For every permitted witness decomposition the input inequality holds and the transformed inequality fails at error zero. |
| `not_concaveSpectralTransferConjecture` | Unconditional negation of the complete original all-parameter, all-function, all-basis implication. |

The source's larger contour-method ratio, separate Nyström sketch identity, ancillary nuclear-norm result and stronger extensions are outside these exports. The smaller proved positive gap suffices for the full canonical negative answer.

## Exact algebra and material LeanCert certificate

The [numerical targets](NUMERICAL_TARGETS.md) and [source correspondence](SourceCorrespondence.md) were specified and reviewed before implementation. Exact compression and finite-dimensional kernel arguments establish actual spectral location and the fourth eigenvalue. A scalar polynomial minorant and genuine CFC order then reduce the strict norm failure to three rational matrix-vector products. An unnormalized vector avoids square roots; symmetry reduces a degree-six quadratic form to six squares.

With `w = (4,3,1,0,0,0)` and `||w||^2 = 26`, the actual minorant Rayleigh value is

```
26 t (1 + gap),
gap = 78605142319958855341529309 / 11432529876841442781954048000.
```

[Numerical](NLA/RA08/Numerical.lean) uses `interval_decide (trust := kernel)`. Its retained helper `NLA.RA08.numerical_gap_positive_proved._proof_1_7` proves the actual strict-upper-bound Boolean checker for constant zero on the singleton `[0,0]`, with the displayed positive rational as the strict upper bound, precision `-53` and nominal depth `10`. The helper is proved by kernel reduction, and `LeanCert.Validity.verify_strict_upper_bound_dyadic_checked` supplies the strict real inequality. The resulting term is consumed by the Rayleigh contradiction and complete conjecture negation.

There is no interval subdivision or numerical spectral enclosure. No native execution trust, assumed operator monotonicity of `min(x,1)`, presumed numerical spectrum or unproved CFC identity is used. The [proof map](PROOF_MAP.md) records the actual algebraic and analytic dependencies.

## Review and checks actually performed

Two frozen statement approvals preceded implementation. The [proof freeze](verification/proof-freeze.json) binds 450 project inputs and ten original Git source files. Candidate packaging retains the exact historical [statement-stage README](verification/pre-candidate-README.md) and [statement-stage manifest](verification/pre-candidate-formalization.yaml); the other 448 proof inputs and 37 statement inputs remain unchanged. The numerical plan and source correspondence stay as historical boundary evidence.

The main implementation and selected-basis CFC identification were written by `/root/formal_review_standards`; `/root` contributed generic spectral/norm lemmas and the disclosed compression route; `/root/solved_statement_inventory` proved ordered spectral existence. Both historical statement reviewers later contributed implementation and are not independent final mathematical referees.

The independent [first final report](reviews/final-referee-1.md), by `/root/leancert_examples`, and [second final report](reviews/final-referee-2.md), by `/root/mf16_final_referee`, approve the exact complete mathematics. Their sealed inventories bind all raw checks and this distinction of roles. [Coordinator acceptance](verification/final-review-acceptance.json) records both reports and inventories; the coordinator is a disclosed coauthor and does not supply an independent mathematical approval. The first referee ran twenty successful fresh commands and recorded 61 standard-three axiom reports; the second ran nineteen successful commands and recorded 62. Their actual type-and-body traversals independently reached 215 project declarations from the full negation, checked the material LeanCert dependency, and inspected the complete CFC, norm, spectral and truncation chain. Both independently reconstructed the exact rational witness and polynomial data.

The final author validation ran nineteen successful fresh direct-source commands, including all sixteen mathematical modules, Solution, an actual dependency inspector, and separately Challenge. It recorded 59 standard-three axiom reports and associated kernel assertions. Implementation and successful inspections had no warnings. Only the fourteen separate intentional Challenge placeholders warned. Raw development failures and reviewer-tool corrections are retained and distinguished from successful proof checks; they did not alter the frozen mathematics during review.

Each local check started with an empty private project prefix. Only the ten exact clean MI-22 dependency source/artifact directories were reused read-only; no previous RA-08 or MI-22 project objects were imported. These were macOS source checks, with no Lake build, dependency copy, download or dependency rebuild. They are not Linux or Comparator results.

The solution does not import Challenge and has no admission or custom axiom. All fourteen exports are selected by the [Comparator configuration](comparator.json), which permits no replaceable definitions and only `propext`, `Classical.choice` and `Quot.sound`. Comparator checks formal statement identity; the independent statement reviews check correspondence to the original mathematical problem. The [v0.4 metadata](formalization.yaml) binds the exact reports and inventories.

## Reproduction and remaining gates

Lean is pinned to 4.33.1, Mathlib to `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert to `621a43d7cf21f87872392a01e874f2f1dbddc926`. All ten dependency pins are in [lake-manifest.json](lake-manifest.json). On a checkout with those dependencies installed, explicitly build the implementation:

```
lake build Solution
```

The unchanged default Lake target is `Challenge`; plain `lake build` checks the reference statements and does not prove them. Actual Ubuntu verification must run the pinned Comparator for all fourteen exports, default-kernel replay and both real control suites. Independent operational acceptance and publication review are also required before any canonical **Lean verified** promotion.

The campaign applies the repository's [Tau Ceti-based review protocol](../../../docs/lean/REVIEW.md) and credits the pinned Schiffer and Forsythe organization/trust examples in its source correspondence and metadata. No human peer review, official Tau Ceti endorsement, source-author endorsement or new mathematical priority is claimed.
