# IS-03 independent statement referee 2

**Verdict: APPROVE the frozen statements for proof implementation. No mathematical correction is requested.** This is a statement-stage approval, not approval of a completed proof or a Lean-verified status.

Reviewer: `/root/formal_review_standards`, an independent Codex AI agent, 12 September 2026. The root and statement-inventory agents authored the statements; I authored neither those statements nor a proof. I performed my own semantic inspection, three fresh source elaborations and exact rational reconstruction. The other referee notified me of its result; I did not use its report, calculations or compiler logs as evidence for this verdict. The two agent reviews are not external human peer review.

## Exact reviewed boundary

| File | SHA-256 |
| --- | --- |
| `reviews/statement-freeze.json` | `588196a54decb127a814dc4860621505d6874a077295f3e30a782d7f28b8ac6c` |
| `reviews/statement-handoff.md` | `3c1d998ba3d3a658a7d9ea706e4357ab3587757050cef70e6f366481affd7c68` |
| `NLA/IS03/Definitions.lean` | `8b4b581e9831b0438d0635b013a60df0cf0139fa9087850b842d8e58975ea1a9` |
| `Challenge.lean` | `4a8817f7c983819fac0a9206092831e72709fcfdb73b0687350914162ef23440` |
| `NUMERICAL_TARGETS.md` | `b1fe777e2d4853b4d60d75e4d0628939f19434434ca82ac4ffe2a3e5bdbf1787` |
| `comparator.json` | `f1e84761b1175d1d638b6cc26c2c2797c7da64ca7dd73919594437388484bf0a` |

All **34 frozen project files** and **10 original source files** remain byte-identical. I checked every original against its recorded Git blob at `f41f1f9ffa2171550d4bb795862c6170c4f26070`. The original manuscript is `references/colbrook-additional-2026-09-11/original-manuscripts/IS-03.md`, SHA-256 `548553e2f177da2a2c5135030c6a34fff761d2b9c800b246b7f9a6797e02d45c`. The complete original manuscript, canonical statement, authored solution, generated TeX, original informal review, submission/preservation notes and relevant source manifest were inspected. The IS-03 part of the supplied diagnostic was read for context; my reconstruction does not import or execute that diagnostic. Unrelated checks in that multi-problem file are outside this review.

The evidence directory contains the complete frozen input record, original Git identities, final integrity check, inspected primary-library hashes, commands and raw outputs. `Solution.lean` and `NLA/IS03/Proof.lean` do not exist. No source, statement, pin, configuration, canonical status, index or original manuscript was changed.

## Original target and all seven contracts

`DerivativeRealizabilityConjecture` is the complete canonical universal assertion: every natural order `n ≥ 5`, every **real entrywise-nonnegative** square matrix `A`, and a real entrywise-nonnegative matrix `B` of **exactly** order `n - 1`, with polynomial equality `B.charpoly = ((n : ℝ)⁻¹) • A.charpoly.derivative`. Natural subtraction is harmless under `n ≥ 5`. No symmetry, irreducibility, zero-trace condition, invertibility, simple spectrum, diagonalizability or real-root assumption is added. The reciprocal is real division, not integer division. Polynomial equality has not been replaced by pointwise sampling or a list surrogate.

I inspected the elaborated definitions with `pp.all`, the actual matrix power instance, and the pinned implementation sources. `RealMatrix n` is Mathlib's `Matrix (Fin n) (Fin n) ℝ`; `EntrywiseNonnegative` is real entry order, not positive-semidefinite order. `Matrix.semiring` uses matrix multiplication, whose entries are sums of products. Its natural powers are not entrywise powers. `Matrix.trace` sums diagonal entries. `Matrix.charpoly` is the determinant of `X I - A`; `Polynomial.derivative` is the actual formal derivative and the scalar action is the ordinary real polynomial action. No local instance, new elaborator, custom axiom or substitute truth predicate changes those semantics.

| Export in `NLA.IS03` | Independent assessment |
| --- | --- |
| `nonnegative_power_trace` | Correctly covers every matrix order and every natural power. Dimension zero has an empty trace; power zero is the identity. These edge cases are compatible with the conclusion and introduce no premise into the original conjecture. |
| `witness_admissible` | Uses the actual 49-entry matrix `diag(1/2,C₂,C₄)`, with nonnegativity and genuine trace `1/2` as conclusions. The reducible, positive-trace witness is allowed by the target. |
| `witness_polynomials` | Requires proving equality of the actual characteristic polynomial to the proposed `p`, then equality of the actual normalized derivative to the explicit `q`, plus monicity and degree six. Neither equality is installed by definition or assumed. |
| `trace_moment_certificate` | Quantifies over **every** real `6 × 6` matrix `B` with the sole premise `B.charpoly = q`. The seven actual traces are conclusions. Even nonnegativity is not assumed here. `i : Fin 7` and exponent `i.val + 1` represent powers one through seven. |
| `negative_moment` | Index `6 : Fin 7` is the seventh moment. Both its exact rational value and its strict negativity are required. The statement does not assert that a scalar certificate has already run. |
| `counterexample` | Asserts admissibility of the actual witness and exclusion of every entrywise-nonnegative real order-six realization of its **actual** normalized derivative. |
| `not_derivativeRealizabilityConjecture` | Negates the full all-order conjecture without additional assumptions. Specializing that conjecture at the admissible order-seven witness will suffice. |

The source's stronger exclusion after arbitrary zero padding, the separate moment-conjecture consequence, minimal-order questions and historical priority are outside these exports. Omitting those extras does not weaken the negative answer to the original exact-order target.

## Independent arithmetic and proof feasibility

My standard-library `Fraction` diagnostic parses the actual frozen Lean matrix, polynomials and moment literals. It independently expands the sparse polynomial determinant, differentiates it, applies Newton's recurrence, and also computes the characteristic polynomial and seven actual powers of a companion matrix. The witness determinant has four supported permutations; the companion determinant has six. There is no floating-point root calculation or numerical eigensolver.

The actual witness determinant has ascending coefficients

```
[-1/2, 1, 1/2, -1, 1/2, -1, -1/2, 1].
```

Dividing its formal derivative by seven gives exactly the displayed monic degree-six `q`. Both independent moment routes yield

```
[3/7, 79/49, 48/343, 6731/2401, 5213/16807,
 219766/117649, -8593/823543].
```

In particular, the six numerator contributions to `7 s₇` at denominator `7⁶` are
`659298 + 182455 - 659638 + 49392 - 189679 - 50421 = -8593`.
The diagnostic also checks witness powers zero through seven and the empty-matrix convention. As an optional feasibility check it derives the factorization of `q` by `X² - 1` and exact rational Bézout coefficients satisfying `q u + q′ v = 1`. None of these Python checks is a Lean certificate or a universal trace theorem.

The essential remaining proof obligation is genuine: transfer the coefficients of the characteristic polynomial to traces of powers for an arbitrary eligible matrix. The inspected Mathlib [Newton identities](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean) are identities of symmetric multivariate polynomials. They require a proved bridge to spectral data and matrix traces. The [trace/roots interface](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Matrix/Charpoly/Eigs.lean) uses the root **multiset** with algebraic multiplicity. A set of eigenvalues loses needed information. Applying the trace-only result to `B^k` does not itself identify its roots with powers of the roots of `B`.

A companion-matrix calculation alone therefore cannot close `trace_moment_certificate`. Cayley–Hamilton by itself supplies a recurrence but does not establish the first six traces. A spectral implementation must prove the complex transport and trace-power bridge, with any separability or diagonalizability fact derived from `q`; a fully proved algebraic alternative is equally acceptable. No such missing bridge is present as an assumption in the frozen statements.

Reuse is feasible without new surrogate machinery. In particular, `Matrix.pow_apply_nonneg` already supplies entrywise nonnegativity of all powers; the trace conclusion follows by summing diagonal entries. The actual block/reindex characteristic-polynomial API, `Polynomial.coeff_derivative`, `Matrix.trace_eq_neg_charpoly_coeff`, `Matrix.aeval_self_charpoly`, and `Matrix.pow_eq_aeval_mod_charpoly` were located and inspected. The seven exported contracts have concrete downstream consumers; this does not request duplicating those library proofs.

## Fresh local checks and trust boundary

I ran three fresh source elaborations in order: `NLA/IS03/Definitions.lean`, `Challenge.lean`, and my independent `Inspect.lean`. All returned zero. Definitions and inspection have no warnings; Challenge has exactly its **seven deliberate `sorry` warnings**. Each command's arguments, source/object/log hashes, runtime and full `LEAN_PATH` are retained. The separate output prefix was `/tmp/nla-is03-statements-ref2-mtab0tb0`; old IS-03 and MI-22 project objects were excluded. The matching MI-22 package objects were reused read-only. This is a local macOS source re-elaboration, not fresh dependency compilation or Linux verification.

All ten dependency Git revisions match the manifest and remain clean. Lean is `4.33.1`, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; Mathlib is `0df444a360eaa60ab8c11dca51a86af692955474`; LeanCert is `621a43d7cf21f87872392a01e874f2f1dbddc926`. Nine directly inspected primary-library files are independently bound to their immutable Git blobs.

My inspector runs eight **definition-only** `#assert_trust kernel` checks and prints their transitive axioms. Each has exactly `propext`, `Classical.choice`, and `Quot.sound`. I inspected LeanCert's actual `collectAxioms`-based command and its rejection of `sorryAx`, custom axioms and native-compiler trust in kernel mode. The two printed Challenge theorem closures deliberately include `sorryAx`, making the admitted status explicit. Definition checks do not prove the seven contracts.

The comparator configuration lists exactly those seven names, no definition exceptions, and only the standard three permitted axioms. Its Challenge/Solution modules are separate. No Comparator or authoritative Linux check has run at this stage; future Solution imports must exclude Challenge.

The numerical plan is economical: one kernel LeanCert point certificate for `(-8593/823543 : ℝ) < 0`, to be retained in the negative-moment theorem and the final trace contradiction. All characteristic-polynomial, derivative, universal matrix and recurrence identities still require exact proofs. There is no reason to approximate roots or subdivide intervals. I did not execute the future scalar certificate or claim that its consumer chain already exists.

One diagnostic attempt initially failed because Python's expression parser needed parentheses around the multiline Lean polynomial text. I retained the original diagnostic and failure record, then corrected only the parser wrapping; no numerical token or Lean source changed. The corrected reconstruction passes. The three independent Lean commands passed without a repair or repeat.

## Review standards, documentation and remaining gates

I applied all ten pinned [Tau Ceti review angles](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics) through this repository's `docs/lean/REVIEW.md`, with the rubric hashes retained. Scope is one permanent NLA target, not a claim of Tau Ceti roadmap admission. Correctness and generality are covered above; proof quality is assessed only as a plan because no proof exists. Reuse and API inspection found ordinary Mathlib operations with explicit obligations. The `NLA.IS03` namespace, project placement and conclusion-oriented names identify this target without global notation or compatibility machinery. Each mathematical definition and public contract has an explanatory comment.

The live README, numerical plan and source correspondence accurately disclose the statement-only phase, full target, excluded stronger claims, substantial trace bridge and pending Linux gate. They credit Matthew J. Colbrook's mathematics, Johnson and the cited original source, and George Stepaniants's AI-assisted formalization with the **Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA**. No George email has been added. Source preservation and the included Apache license do not reassign or relicense the original manuscript.

After root accepts both independent statement approvals, implementation may proceed while retaining these exact statements. Before any Lean-verified promotion, the completed proof needs two independent final reviews, materially consumed kernel-only numerical evidence, transitive standard-three closure, exact Challenge/Solution comparison and the real sandboxed Linux/default-kernel controls. This review supplies none of those later approvals by anticipation.

Evidence: [statement-referee-2-evidence](statement-referee-2-evidence/), with its complete file manifest and offline verifier. The report's own hash is recorded in that manifest.
