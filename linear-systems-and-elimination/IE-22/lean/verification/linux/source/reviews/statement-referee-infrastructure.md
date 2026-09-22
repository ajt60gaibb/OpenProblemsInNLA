# IE-22 independent preproof statement review

Verdict: **APPROVE these exact statements for proof implementation after the second independent approval and explicit freeze.** No mathematical-target or numerical-constant defect was found. This is a preproof statement review, not verification of IE-22, not final publication approval and not external human peer review or official Tau Ceti endorsement.

Reviewer: Codex AI agent `/root/infrastructure_audit`, 2026-09-22. I authored **none** of IE-22's definitions, Challenge statements, numerical inventory or Comparator selection. I authored six reused IE-21 modules (SphericalLaw, RowLaw, GaussianPolar, GaussianMoments, SphericalMoments, SphericalMGF). That transitive authorship is disclosed: this review is independent of the new IE-22 boundary author, but I cannot serve as a fresh nonauthor final referee of the combined future proof package.

I read the complete canonical IE-22 README, the complete retained joint IE-21/IE-22 manuscript, all new definitions, all 20 Challenge statements, all NUMERICAL_TARGETS.md, the Comparator configuration and the supplied dependency/typecheck records. The numerical inventory reproduces the complete canonical problem-statement section byte for byte after trimming surrounding whitespace; an explicit script comparison passed. Original ID/path and Matthew J. Colbrook's proof attribution remain preserved. George Stepaniants and the specified Caltech department affiliation appear without adding a contact email.

The exact reviewed boundary is:

| File | SHA-256 |
| --- | --- |
| `NLA/IE22/Definitions.lean` | `206dd0bc8af86b5a67541985a9ba209472cf6788dba7120b8adaf00545fba371` |
| `Challenge.lean` | `03336766670095f08f74eb9d6a0704ed8812ca9cde31a99d2a2fbc6521a11152` |
| `NUMERICAL_TARGETS.md` | `31d41813f8e6c7952d5d197e0b2246dfa79dfe8c6ffab56fdb0c64a4d5d4334e` |
| `comparator.json` | `f625c401bf276a2e93b7e76b2b052555c8686b57590fd7da16fdb56e2840c7a8` |

`normalizedSingular` is sqrt(n/m) times the variational retained-row singular value, not the squared statistic or the IE-21 ratio divided by the operator norm. `extremalValue` is the supremum over all actual unit-row real matrices. Its mandatory semantics prove the set nonempty and bounded above, attainment, domination of every matrix, nonnegativity and the square relation to normalizedDeletion. Thus real sSup defaults cannot replace the canonical extremum. Positive dimensions make the unit sphere nonempty; the exact natural floor remains unchanged. Zero retained rows and rank deficiency are permitted, with no hidden full-rank or k≥n assumption.

Every selected obligation was checked:

| Declaration | Correspondence and critical conditions |
| --- | --- |
| `supremum_semantics` | Literal finite-dimensional unit-row extremum and attainment; unsquared/squared bridge for positive m,n. |
| `constant_semantics` | Actual sqrt of the canonical Gaussian density integral, with nonnegativity and its square; unique cutoff semantics are inherited unchanged from IE-21. |
| `projection_semantics` | Actual restriction along a Euclidean isometry, contracting row norms, and the correctly directed sθ(A)≤sθ(B). Allows m=0 only in this valid auxiliary identity. |
| `spectral_projection` | Existence of the n−r dimensional isometry is a conclusion; 1≤r<n and m≥1 give positive retained dimension, op-norm squared ≤m/(r+1), row contraction and trace bound. |
| `gaussian_objective_mean` | For all t≥0, actual standard Gaussian expectation ≤hθ under row norms ≤1; no independence between projected rows and no nonzero-row premise. |
| `gaussian_objective_variance` | Actual MemLp 2 and Var≤4t·opNorm²/m are obligations, with exact factor four. Arbitrary θ is harmless because its contribution is constant in g. At t=0 the objective is identically zero. |
| `gaussian_energy_moments` | Actual quadratic Gaussian mean trace(BᵀB)/m and variance 2 trace((BᵀB)²)/m², with second-moment integrability. Correlated or zero rows are included. |
| `bounded_trimming_threshold` | Exact floor-count primal/dual attainment in [0,L] from average≤2, including k=0. |
| `threshold_lipschitz` | The exact constant one, using k/m∈[0,1]; a generic constant-two bound would not satisfy this statement. |
| `threshold_grid` | Actual interval centers, cardinality ≤L/δ+2 and covering radius δ for every δ>0. |
| `projection_good_event_bound` | Full all-threshold event, explicit measurability, and all three exact probability terms; no restriction to only a finite grid. |
| `deterministic_finite_bound` | The source boxed inequality for every unit-row A, no aspect-ratio condition; strict failure budget<1 and r<n, δ<1 enable a nonzero witness and valid normalization. |
| `supremum_finite_bound` | Same boxed bound for the square of actual M and its square-root bound, connected through attained supremum semantics. |
| `deterministic_schedule` | Literal floor(n^(2/3)) and n^(−1/6), with real exponents, eventual admissibility, vanishing error and Oθ rates for both failure and bound error. |
| `universal_squared_rate` | C and N depend only on θ; bounds hold for all m≥1, n≥N, all unit-row A, and M². |
| `uniform_upper_all_rows` | For every ε>0, one N works for every m≥1 and n≥N, the manuscript's stronger upper claim without an aspect restriction. |
| `spherical_realization_from_finite_bound` | An actual unit-row deterministic witness from IE-21's normalized numerator bound and strict positive-probability budget; not an unsupported inference from its ratio limit alone. |
| `high_aspect_near_extremizers` | For every positive sequence with n→∞ and m/n→∞, eventually actual witnesses exceed cθ−ε; no additional growth rate or common probability-space hypothesis. |
| `high_aspect_supremum_limit` | The actual supremum converges to cθ along every such sequence, retaining both upper and lower conclusions. |
| `canonical_sharp_constant` | The exact original eventual-uniform property holds for cθ and fails for every real smaller C. |

The finite constants agree exactly with Sections 6–7: L=2/(1−θ), projected dimension d=n−r, failure 2/(r+1)+4L(L/δ+2)/((r+1)δ²)+2/(dδ²), and boxed upper bound n/((n−r)(1−δ))·(hθ+2δ). The gradient/Poincare route gives 4t·opNorm²/m, then 4t/(r+1); energy variance gives the first failure term and radius variance 2d gives the last. The one-Lipschitz grid extension accounts for 2δ, with no enlarged constants. The proposed schedule has leading failure order n^(−1/6), and its explicit existential rate constant is exactly the manuscript's Oθ content, not an omitted fixed numerical certificate.

The final quantifiers are correct: ε is outside the existential N,R and all matrices/dimensions. Failure for a smaller C therefore requires a fixed ε defeating every pair of thresholds. Natural thresholds faithfully represent the stated integer thresholds by increasing negative ones to zero. Every-sequence convergence remains separately selected and cannot be replaced by one diagonal construction or an upper limsup. The stronger all-m upper statement does not weaken the canonical high-aspect assertion.

No final theorem assumes a desired spectral reduction, a Poincare inequality, the trimmed-Gaussian mean, or the sharp conclusion. Those facts are selected proof obligations or unchanged proved IE-21 inputs. The exact Gaussian variance obligation is substantial new analysis; its difficulty or a missing library API does not justify weakening its constant or replacing it with an axiom. The complete 20-declaration selection agrees exactly with Challenge; `definition_names` is empty and future permitted axioms are only propext, Classical.choice and Quot.sound.

Independent statement-only typechecking used `reviews/statement-referee-infrastructure-evidence/typecheck.py` and a fresh reviewer output directory. Definitions and Challenge both returned exit 0, with exactly 20 deliberate Challenge-placeholder warnings and no other Lean diagnostics. The first reviewer invocation failed only because Lean's root-module search did not combine two NLA output roots; its original script/log are retained. The reviewer build was corrected to link the unchanged IE-21 cache under the new output's NLA directory, and the successful run used a new output directory. No boundary or dependency source was changed to resolve that local path issue.

All 31 reused IE-21 source hashes were independently matched to publication input `1eb284b84ecc0d3c958d022b3e020be7fa111391` and its successful authentic Linux source/result receipts, with distinct Linux guest commit `bd72d630841a1660b9f7652d469186c11728925f`. The reused local final-fidelity dependency oleans are separately hashed in this receipt. This typecheck did not rebuild those oleans or every Mathlib dependency; their cache provenance and my authorship are disclosed. It proves only well-typed reference statements, not any IE-22 theorem. No IE-22 Solution or proof module exists.

Reproducible IE-22 packaging must still bind the unchanged IE-21 inputs to immutable verified source, and all implementation/final-review/LeanCert/Comparator gates remain required. A mutable cross-worktree path is not acceptable publication evidence. This unresolved packaging work does not change the reviewed mathematical boundary or supply an assumption to it. The corrected numerical inventory accurately records that IE-21's Linux run has passed while completion/publication review is separate.
