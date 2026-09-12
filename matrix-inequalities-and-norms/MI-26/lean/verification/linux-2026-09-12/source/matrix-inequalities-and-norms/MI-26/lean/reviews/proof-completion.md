# MI-26 complete local proof, frozen for independent final review

**Implementation complete — 12 September 2026.** The full seven-export
`Solution` built successfully in a **3,147-job** graph using Lean 4.33.1.
The actual Proof and Solution modules were freshly elaborated, with no
warnings. All **15** internal/public explicit kernel-trust assertions passed,
and every printed transitive axiom set is exactly `propext`,
`Classical.choice`, and `Quot.sound`. This is the implementer's completion
record, not an independent final referee report or a Linux verification.

The actual [build record](../verification/proof-build.json),
[successful log](../verification/proof-build.log), and
[axiom inventory](../verification/proof-axioms.json) are retained.
The existing matching dependency artifacts were reused in the isolated
project; this is local macOS elaboration, not a fresh dependency rebuild.
All ten pinned dependency HEADs and tracked sources remain unchanged.

## All seven reviewed exports are implemented

1. `admissibleFunction_iff` proves both directions of the exact canonical
   half-line θ-concavity condition, together with the condition at zero.
2. `functionalCalculus_eq_spectral` identifies genuine real CFC with the
   actual Mathlib eigenvalue/eigenvector-unitary formula for every Hermitian
   complex matrix and every real function, without any continuity premise.
3. `functionalCalculus_congr_nonneg` uses the actual nonnegative eigenvalues
   of PSD matrices to prove that arbitrary negative-argument extensions do
   not affect the CFC value.
4. `quadratic_cfc` proves the generic genuine-CFC identity
   `cfc (t ↦ t-t²) A = A-A²` at every Hermitian matrix.
5. `witness_data` proves every scalar admissibility, complex PSD, projection,
   CFC, nonzero-vector and exact quadratic-form obligation from the frozen
   interface. None is an added hypothesis.
6. `counterexample` excludes every pair of genuine complex unitaries at the
   exact rational witness.
7. `not_subadditivityConjecture` negates the full original all-dimension,
   all-PSD-complex-input, all-real-valued-concave-function conjecture.

The [source-level signature comparison](../verification/proof-statement-identity.json)
matches all seven Solution declarations to the unchanged Challenge. The
real Linux Comparator remains a separate verification gate.

## Analytic proof and minimal numerical certificate

Concavity follows from the exact universal Jensen-gap identity
`θ(1−θ)(x−y)² ≥ 0`; finite samples and derivative assumptions are not used.
Actual complex Gram identities prove P and Q PSD. Their projection and
matrix-polynomial identities are exact two-dimensional algebra. The generic
polynomial CFC theorem binds those computations to the original matrix
function, yielding `f(P)=f(Q)=0` and
`f(P+Q)=[[-18,-12],[-12,0]]/25`.

The exact complex quadratic form at `w=(1,-2)` is `6/5`. The only interval
computation is the explicit kernel LeanCert point certificate `0 < (6/5:ℝ)`
on the degenerate interval `[0,0]`. No subdivision, eigenvalue calculation,
matrix-root approximation or unitary search is needed.

If the proposed inequality held, actual `Matrix.PosSemidef` would make the
quadratic form of the negative image nonnegative. The proof uses
`Matrix.PosSemidef.dotProduct_mulVec_nonneg` and `Complex.nonneg_iff` to
derive the real inequality `0 ≤ -6/5`, then explicitly applies
`not_le_of_gt (neg_neg_of_pos witness_positive)`. Thus the certificate is
retained in the contradiction rather than bypassed by an independent
closed-scalar simplifier. The complete negation consumes that contradiction.

The [actual printed proof terms](../verification/proof-inspection.log) show
`LeanCert.Validity.verify_strict_upper_bound_dyadic_checked`, the zero-width
point, its direct use in the all-unitary exclusion, and the final negation.
They also show that the generic spectral bridge elaborates directly to
`Matrix.IsHermitian.cfc_eq`, with no new CFC premise or fallback argument.

## Frozen boundary, trust and remaining gates

Both independent statement approvals preceded creation of any implementation
proof, as recorded in [proof-start.json](../verification/proof-start.json).
Their exact hashes and the approved Definitions, Challenge and numerical
plan are unchanged. Earlier failed build logs are preserved: the fixes were
a library namespace, simplification of conjugated numerals, and `using!`
for definitionally equal matrix instances. No mathematical statement was
changed. Proof and Solution contain no `sorry`, `admit`, custom axiom,
unsafe declaration or native tactic, and never import Challenge. Its seven
deliberate placeholders remain exclusively in the frozen statement template.

| Frozen mathematical file | SHA-256 |
| --- | --- |
| `NLA/MI26/Definitions.lean` | `821cb1b2a29f7382a1f36bd6b506bc6b249b9da0b61837702658173814995f63` |
| `Challenge.lean` | `85eafac2fc875ddacb35c37f832834cfe79e6b10730f2656185209592f608fe1` |
| `NUMERICAL_TARGETS.md` | `ecc403bb0f57fc49f2e3be78c9012f7e606ca8035d92af83fa95bddfbe994257` |
| `NLA/MI26/Proof.lean` | `94dd1dde3f1b12002380ae4730ea6396a955f7cbe69a34dde101e7a035fae0af` |
| `Solution.lean` | `a79aa8df0b6b7501dcb6d264fc8a9a21ac0710aa05ed65bff3b244ba97fe6da1` |

The complete input/evidence freeze is
[proof-freeze.json](../verification/proof-freeze.json). Two independent final
proof reviews, truthful completed-project metadata, actual Linux Comparator
and its independent operational audit remain required before promotion.
The canonical MI-26 target, informal manuscript and status are unchanged;
no MI-26 commit, push, or PR was made by this implementer.

The proof resolves the complete canonical PSD-input, real-valued function
assertion. The source's stronger positive-definite variant is not claimed
as an export. The narrower globally nonnegative function class is not
contradicted. Mathematical proof: **Matthew J. Colbrook**, Department of
Applied Mathematics and Theoretical Physics, University of Cambridge.
Formalization: **George Stepaniants**, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA,
with AI-agent assistance and without his email. No external human peer review,
source-author endorsement or historical-priority claim is made.
