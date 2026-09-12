# MI-26 independent statement referee 2 — PASS

Date: 12 September 2026. Reviewer: OpenAI Codex agent `/root`, independent of statement author `/root/leancert_examples`. **Approve the frozen seven-export interface for implementation. No statement correction is required.** This is a statement and numerical-specification review, not a completed proof or Linux verification.

I independently read the full canonical README, Colbrook's complete source TeX, Definitions, Challenge and the numerical plan. I inspected the actual pinned Mathlib definitions, compiled the declarations into a fresh artifact prefix and printed their elaborated semantics. I also reconstructed the witness with exact rational arithmetic. These checks and their conclusions were completed before reading referee 1's final report. The original source files remain identical to upstream `587bd896f0e1006f4a4b7f38555e3a523ef85176`; no Proof or Solution implementation existed at this boundary.

## Complete original target

`SubadditivityConjecture` retains every positive dimension, arbitrary complex PSD matrices A and B, and every real-valued concave function on the nonnegative half-line satisfying f(0) ≥ 0. Two arbitrary complex unitaries are existentially quantified after those inputs. The proposed comparison is the actual PSD order: fresh elaboration uses `Matrix.instPreOrder`, whose defining relation is positive semidefiniteness of right minus left. The pinned source `Mathlib/Analysis/Matrix/Order.lean` identifies this relation explicitly. This is not pointwise matrix order or a norm comparison.

`AdmissibleFunction` has exactly `ConcaveOn ℝ (Set.Ici 0) f` and the value-at-zero condition. I checked the library's two-nonnegative-weights definition of concavity against the θ formulation in the canonical page. The fixed half-line is convex, so the domain-convexity component adds no restriction on f. The first export requires their full equivalence, including both directions and every θ in [0,1]. No global nonnegativity, monotonicity, continuity or positive-definiteness requirement has been added.

Using a function on all of ℝ does not narrow the original half-line class: every half-line function extends by evaluation at max(x,0). Conversely, restriction recovers a valid original function. The admissibility predicate only inspects the half-line. The third export requires a generic proof that any two such extensions give the same actual CFC at every PSD input. This excludes dependence on arbitrary negative-argument values.

## Functional calculus and exported obligations

`functionalCalculus f A` is genuine real `cfc f A` in the complex matrix algebra. I read the pinned `Matrix.IsHermitian.cfc` spectral definition and `cfc_eq`: they use the actual eigenvalue list and eigenvector unitary. Equality with general CFC needs no global continuity assumption, because every function on the finite spectrum is continuous there. Hence the interface also represents concave functions that may be discontinuous at the endpoint of the whole half-line. It does not rely on a fallback value at a non-Hermitian input: PSD matrices and their sum are Hermitian.

The seven exports are adequate and have the following scopes:

- `admissibleFunction_iff` exposes exactly the original scalar concavity definition.
- `functionalCalculus_eq_spectral` links genuine CFC to actual spectral theorem objects for every Hermitian matrix and every real function, without a continuity premise.
- `functionalCalculus_congr_nonneg` proves extension invariance on every PSD input.
- `quadratic_cfc` links the witness polynomial to A−A² for every Hermitian matrix; A² is a matrix-ring power.
- `witness_data` must prove admissibility, PSD, projection identities, all actual CFC values, the nonzero vector and its exact positive quadratic form. These are conclusions, not extra hypotheses.
- `counterexample` excludes every pair of complex unitaries at the explicit witness.
- `not_subadditivityConjecture` unconditionally negates the complete original universal conjecture.

The generic bridges deliberately expose the semantic steps that a polynomial-only replacement would hide. The proposed final proof may specialize to a polynomial witness, but the conjecture being negated remains the full real-valued function statement. No narrower theorem about globally nonnegative functions is contradicted or claimed. The source's stronger positive-definite variant is outside this certificate.

## Exact numerical specification and analytic reduction

My independent Fraction calculation checks P=diag(1,0), Q=[[9,12],[12,16]]/25, their projection identities and the matrices

P+Q=[[34,12],[12,16]]/25,
(P+Q)²=[[52,24],[24,16]]/25,
F=[[-18,−12],[−12,0]]/25.

P and Q are outer products of the unit vectors (1,0) and (3/5,4/5), so the proposed complex PSD certificates are sound. For f(t)=t−t², f(0)=0 and f(2)=−2. Its concavity is the universal analytic identity with Jensen gap θ(1−θ)(x−y)²≥0, not an inference from finite samples. Actual CFC equality with the matrix polynomial remains a Lean proof obligation.

For w=(1,−2), exact multiplication gives Fw=(6/25,−12/25), w*Fw=6/5>0 and w≠0. All tabulated entries match the approved definitions. The two projection images are zero, so every pair of unitary conjugates on the right is zero. If the proposed inequality held, −F would be PSD and its quadratic form at w would be nonnegative, contradicting −6/5<0. The proof must explicitly bridge actual complex PSD nonnegativity to that scalar contradiction. It cannot replace matrix order with a custom scalar predicate.

Only the positive rational scalar 0<6/5 needs the planned explicit kernel-mode LeanCert certificate, and the final contradiction must retain that certificate. No interval subdivision, eigenvalue approximation, search over unitaries, or numerical matrix square root is needed. All matrix equalities can be exact algebra, and the universal concavity and CFC facts remain analytic proofs.

## Checks, review scope and next gates

Definitions, Challenge and a fresh elaboration inspection each exited zero. Definitions and inspection had no warnings; Challenge had exactly seven deliberate placeholder warnings. These templates are statement specifications and must not be imported by Solution. All ten actual dependency HEADs match the manifest and have clean tracked source. Existing pinned dependency artifacts were reused; this was local macOS validation, not remote Linux Comparator or a source rebuild of Mathlib.

The elaboration inspection SHA256 is `e23988ea90d3d78a9232434a748e386bec3b844e353e8d5d7da75c7c87110710`. Raw commands, outputs, dependency identities and the independent rational reconstruction are retained in [statement-referee-2-root-evidence](statement-referee-2-root-evidence/). A subsequent literal diagnostic initially expected an instance named `Matrix.instPartialOrder`; inspection showed the actual correct `Matrix.instPreOrder`, and checking its source definition resolved the diagnostic. No mathematical source changed and no failing Lean command was hidden.

I applied the relevant Tau Ceti faithfulness/correctness, scope, computation, reuse and attribution rubrics at `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`, adapted to this permanent NLA target. This is independent AI-agent review, not official Tau Ceti endorsement or human peer review. The mathematical counterexample remains Matthew J. Colbrook's. Formalization credit is George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI assistance and without his email.

After both statement approvals, implementation can begin. Two independent final proof reviews and actual Linux Comparator signature matching, no definition holes, default-kernel replay and standard-three-only transitive axioms remain required before promotion. No canonical status, Git commit or remote publication was changed by this review.

| Frozen file | SHA256 |
| --- | --- |
| `NLA/MI26/Definitions.lean` | `821cb1b2a29f7382a1f36bd6b506bc6b249b9da0b61837702658173814995f63` |
| `Challenge.lean` | `85eafac2fc875ddacb35c37f832834cfe79e6b10730f2656185209592f608fe1` |
| `NUMERICAL_TARGETS.md` | `ecc403bb0f57fc49f2e3be78c9012f7e606ca8035d92af83fa95bddfbe994257` |

Any substantive statement change reopens the affected independent reviews.
