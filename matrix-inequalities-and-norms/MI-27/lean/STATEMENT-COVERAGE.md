# Mapping from reviewed prose to exact source signatures

All twenty declarations are in namespace `NLA.MI27` and are listed in order in `comparator.json`. Matrix contracts retain every n ≥ 1. The source is unelaborated; this mapping is an author explanation, not an independent approval.

| Contract | Declaration | Content made explicit |
|---|---|---|
| C01 | `half_coefficient_positive` | Positive half, intended consumed kernel-mode LeanCert certificate. |
| C02 | `spectral_function_semantics` | Actual library eigenvector unitary, finite-spectrum CFC equality, spectral trace, Hermitian logarithm, real Hermitian trace. |
| C03 | `normalize_positive_pair` | Derived positive traces and strict densities with exact inverse scaling and reconstruction. |
| C04 | `positive_trace_operator_bound` | PSD trace pairing against Hermitian Y and the Euclidean operator norm. |
| C05 | `positive_commutator_trace_bound` | Exact factor-one trace estimate for all Loewner effects Q. |
| C06 | `positive_part_variational` | Variational bound, attained Hermitian commuting projection, normalized E in [0,1]. |
| C07 | `positive_part_trace_lipschitz` | Dimension factor allowed only for local regularity. |
| C08 | `unitary_flow_semantics` | Both unitary identities, zero, group law, real derivative, preservation of Hermitian/PSD/PD status, trace, complex spectrum and Hermitian entropy. |
| C09 | `hockey_stick_unitary_lipschitz` | Both arguments, all real s,t and γ ≥ 1, no dimension/gamma loss. |
| C10 | `uniform_hockey_stick_cutoff` | One R > 1 for every bundled unitary, two Loewner bounds, endpoint-inclusive vanishing, continuity on [1,R]. |
| C11 | `relative_entropy_finite_hockey_stick` | Integrable finite expression equals ordinary Umegaki entropy for arbitrary noncommuting strict densities. |
| C12 | `weighted_entropy_finite_kernel` | Integrability and exact weighted ordinary-entropy identity, same original two-sided R. |
| C13 | `kernel_integrals` | Both scalar interval-integrability assertions and both exact logarithmic primitives. |
| C14 | `kernel_entropy_mass_bound` | Both nonnegative mass bounds and their sum bounded by binary entropy. |
| C15 | `entropy_trajectory_lipschitz` | Full finite-time entropy change, not an almost-everywhere claim. |
| C16 | `entropy_unitary_mix_derivative` | Actual real derivative of the trace entropy at zero with the checked commutator sign. |
| C17 | `skew_commutator_trace_norm` | Hermitian rotation, exact Gram equality and literal trace-norm equality. |
| C18 | `hermitian_trace_norm_witness` | Norm-at-most-one Hermitian sign witness, including zero K. |
| C19 | `logarithmic_commutator_dual_bound` | Derived h ≥ 0 and the bound for every Hermitian dual test. |
| C20 | `logarithmic_commutator_bound` | The literal full original target, with only original hypotheses and coefficient one. |

C02 quantifies f with `ContinuousOn f (spectrum ℝ M)`; the finite spectrum permits the intended discontinuous-on-ℝ sign function. Its unitary/eigenvalues come from `M.IsHermitian` and are not assumed external data. The generic f statement supplies log, positive part, absolute value and sign specializations. C08 states trace/spectrum/derivative for arbitrary σ, with explicit implications for each Hermitian/positive class; entropy preservation is required for Hermitian σ, which includes every use. Its unitarity is expressed by the two concrete matrix equalities. C10 quantifies `unitary (Mat n)` for the identical mathematical class.

C17 includes the exact Gram equality requested in the prose proof obligation. C19 includes binary-entropy nonnegativity requested before applying C18. These expose required facts rather than adding any input premise. `StrictDensity` expands to precisely PosDef and complex trace one. No entropy identity, abstract trace norm, spectral oracle, simple-spectrum property or final theorem was hidden in a predicate or definition.

C11's substantial internal proof remains missing. The finite cutoff removes final-stage tails, not the noncommutative entropy theorem. C16 also remains missing. The separate supplemental prose routes suggest trace-overlap Taylor bounds and layer-cake/inertia calculations; no helper signatures for those routes have been accepted yet.

Before proof development: root must run local elaboration with the pinned dependencies and compiler limits, retain the exact commands/source hashes/logs, obtain root plus fresh nonauthor reviews of these actual signatures, and freeze Definitions, Challenge and Comparator hashes. No source-author self-approval applies. Before publication: complete local proofs without reference-placeholder dependencies, independently review statement correspondence and proof source, and run the genuine non-root GitHub Linux Comparator/kernel/sandbox checks with exact source matching. No published ID/path or canonical target changes are authorized by this draft.
