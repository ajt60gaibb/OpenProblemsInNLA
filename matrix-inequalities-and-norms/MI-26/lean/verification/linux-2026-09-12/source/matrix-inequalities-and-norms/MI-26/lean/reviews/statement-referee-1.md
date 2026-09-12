# MI-26 independent statement referee 1

**APPROVE the frozen seven-export statement boundary. No mathematical correction requested.**

Date: 12 September 2026. Reviewer: independent agent
`/root/solved_statement_inventory`; author: `/root/leancert_examples`.
I did not author or edit these mathematical statements. This approval concerns
their semantics and exact numerical specification, not an implemented Lean proof.

## Bound files, source, and pins

| Frozen file | SHA-256 |
| --- | --- |
| `NLA/MI26/Definitions.lean` | `821cb1b2a29f7382a1f36bd6b506bc6b249b9da0b61837702658173814995f63` |
| `Challenge.lean` | `85eafac2fc875ddacb35c37f832834cfe79e6b10730f2656185209592f608fe1` |
| `NUMERICAL_TARGETS.md` | `ecc403bb0f57fc49f2e3be78c9012f7e606ca8035d92af83fa95bddfbe994257` |

I read the full canonical README, complete `solution.tex`, attribution/scope note,
and original independent informal review. Their identities, together with the
archived original proof and recorded configuration, were independently checked
against the frozen inventory and Git revision
`587bd896f0e1006f4a4b7f38555e3a523ef85176`. The canonical README has hash
`478e5814b62ebf360cc7a8016a70dc902ac3aa424284c4ce23b528449a72972c`, and the
complete TeX manuscript has hash
`1a26f0d71bf6284d1b5a4c255d48f2318883ded008cd6f778481fe6a8de3bd02`.
All 22 frozen project/source/evidence inputs remained unchanged during this review.

The project pins Lean `v4.33.1`, LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. All ten actual dependency Git HEADs
match the manifest and have clean status. See the
[input identity](statement-referee-1-evidence/inputs-before.json),
[post-check identity](statement-referee-1-evidence/inputs-after.json), and
[dependency evidence](statement-referee-1-evidence/dependencies.json).

## Function-class and spectral semantics

The formal conjecture retains every positive dimension, every pair of complex PSD
inputs, every admissible real-valued function, and existence of two complex
unitaries depending on all these data. The elaborated inequality uses
`Matrix.instPreOrder`, which means right-minus-left is genuinely PSD; its complex
scalar order and Hermitian requirement are preserved. The unitaries are actual
members of `Matrix.unitaryGroup`, not sampled rotations or real orthogonal matrices.

`AdmissibleFunction f` says exactly `ConcaveOn ℝ (Set.Ici 0) f ∧ 0 ≤ f 0`.
Mathlib's extra domain-convexity component is automatic for this fixed half-line.
The first export requires a proof of equivalence with the original θ-concavity
formula for all `x,y ≥ 0` and `0 ≤ θ ≤ 1`. There is no global nonnegativity,
monotonicity, continuity, positive-definiteness, or spectral-separation premise.
The witness's required value `f(2) = -2` explicitly respects the real-valued class.

Representing a half-line function by an unrestricted extension `f : ℝ → ℝ` is
faithful: any original function extends by evaluating it at `max(x,0)`, and every
such extension restricts back to the original domain. Concavity and the value at
zero only inspect that domain. The generic `functionalCalculus_congr_nonneg`
obligation ensures that every two extensions agreeing there yield the same actual
matrix function at PSD inputs. Its PSD premise is precisely what guarantees the
relevant eigenvalues are nonnegative; it adds no premise to the original problem.

`functionalCalculus f A` elaborates to genuine real `cfc f A` in the complex matrix
algebra with self-adjoint predicate and matrix multiplication. I read the actual
pinned `Matrix.IsHermitian.cfc` and `cfc_eq`: they apply any bare real function to
the genuine finite eigenvalue list, conjugated by the genuine eigenvector unitary.
`cfc_eq` has no continuity assumption because every function restricted to the
finite spectrum is continuous. This remains valid if the original concave function
is discontinuous at the half-line endpoint. It does not rely on the CFC fallback
at a non-self-adjoint input: the original PSD inputs and their sum are Hermitian.

The generic spectral export explicitly binds CFC to those Mathlib spectral theorem
objects, rather than assuming a candidate eigenvalue list. The generic polynomial
export separately requires genuine `cfc (t ↦ t-t²) A = A-A²` for every Hermitian
matrix. An explicit elaboration inspection confirmed that these squares use the
natural powers of `Matrix.semiring`, not pointwise powers of entries.

## Seven conclusions and exact witness

| Export | Scope checked |
| --- | --- |
| `admissibleFunction_iff` | Exact equivalence to the canonical scalar concavity formula and `f(0) ≥ 0`. |
| `functionalCalculus_eq_spectral` | All real functions, arbitrary complex Hermitian matrices, actual spectral objects, no continuity premise. |
| `functionalCalculus_congr_nonneg` | Negative-argument extensions are irrelevant at every PSD matrix. |
| `quadratic_cfc` | Genuine CFC agrees with the matrix polynomial for every Hermitian input. |
| `witness_data` | Admissibility, PSD, projection identities, all CFC values, nonzero vector, and the exact positive quadratic form are conclusions. |
| `counterexample` | Excludes every complex unitary pair at the rational witness. |
| `not_subadditivityConjecture` | Unconditional negation of the complete original universal assertion. |

I independently reconstructed `P`, `Q`, their sum and square using exact rational
arithmetic. `P=e₁e₁*` and `Q=vv*`, with `v=(3/5,4/5)` of squared length one, give
genuine complex PSD projections. Their matrix polynomial values vanish. Exact
multiplication gives

`P+Q = [[34,12],[12,16]]/25`,
`(P+Q)² = [[52,24],[24,16]]/25`, and
`F = (P+Q)-(P+Q)² = [[-18,-12],[-12,0]]/25`.

For `w=(1,-2)`, `Fw=(6/25,-12/25)` and `w*Fw=6/5>0` exactly. I also independently
expanded the scalar polynomial concavity gap and verified its factorization as
`θ(1-θ)(x-y)²`, nonnegative on the stated θ interval. The
[reconstruction script](statement-referee-1-evidence/rational_check.py) and
[results](statement-referee-1-evidence/rational-check.json) are supplementary
diagnostics; no such computed fact is moved into a Lean theorem hypothesis.

Because the two right-side CFC terms vanish, their unitary conjugates vanish for
every complex `U,V`. A proposed order domination would force `-F` to be PSD and
hence `0 ≤ w*(-F)w = -6/5` in the actual complex order, contradicting the strict
real scalar. Instantiating the universal conjecture at dimension two with the
proved admissible function and PSD projections therefore gives its full negation.
No numerical search over unitaries, norm surrogate, or eigenvalue approximation
replaces this argument. The stronger positive-definite variant in the informal
manuscript is expressly outside these exports; the original PSD target is complete.

## Fresh elaboration and applicable review standards

Definitions and Challenge were freshly compiled sequentially into a separate
artifact prefix, with the existing project artifact prefix excluded from
`LEAN_PATH`. The actual-instance and matrix-power inspections then ran against
those fresh artifacts. All four commands exited zero. Definitions and inspections
produced no warnings; Challenge produced exactly seven deliberate placeholder
warnings. The seven printed placeholder declarations depend on `sorryAx` and the
standard three axioms, as expected at this statement-only stage. No proof trust
approval is claimed. Existing dependency artifacts were reused at the checked
pins; this was local macOS elaboration, not Linux Comparator replay.

- [Fresh commands and hashes](statement-referee-1-evidence/fresh-checks.json): `e6d86bcf9e8bc1448a3c0c3d832c3d07cab1c9529c96c87d00898b51ccc9bec1`.
- [Actual semantics inspection](statement-referee-1-evidence/inspection.log): `eedcf5a9f3ab91533c14f79a8d2f94a6f083eb88b7d541a410fde575688b91dd`.
- [Power-instance inspection](statement-referee-1-evidence/power-inspection.log): `9ccaee49129570514afc7f331d9c328da0bff7f6d579a7205bc44a52069e6d3d`.
- [Library identities](statement-referee-1-evidence/library-hashes.json) and [placeholder audit](statement-referee-1-evidence/placeholder-audit.json).

I applied the correctness/faithfulness, scope, reuse and attribution angles of the
recorded Tau Ceti rubrics at `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`, adapting
scope to the permanent MI-26 target rather than Tau Ceti's own roadmap. The generic
bridges expose the semantic boundary and can reuse the actual Mathlib spectral
calculus and PSD eigenvalue results; they do not fake missing prerequisites.
The mathematical counterexample remains attributed to Matthew J. Colbrook.
Formalization credit is George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA, without
George's email. This is an independent agent review using adapted rubrics, not
official Tau Ceti or external human approval.

There is no `Proof.lean` or `Solution.lean` at this boundary. Implementation must
await the second independent statement approval. Later proof reviews must check
all seven complete exports, substantive use of the kernel LeanCert certificate
`0 < 6/5`, and standard-three-only transitive axioms. Actual Linux Comparator and
publication remain later gates. I changed no mathematical source, canonical file,
catalog status, commit, or remote state.
