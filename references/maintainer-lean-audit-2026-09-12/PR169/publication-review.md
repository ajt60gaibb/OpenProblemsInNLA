# PR #169 — MI-26 publication review

**Verdict: PASS for publication, metadata consistency, and PDF presentation.** No blocking finding in this review's scope.

- Reviewed head: `38122892d2d6e6e0093a381dbfe2fbae026ac15b`.
- Compared branch base: `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`.
- Date: 2026-09-12.
- Reviewer: Codex, a GPT-6 AI review agent; this is not external human peer review.
- Worktree: `/private/tmp/nla-lean-audit-169`.

This independent review covers publication scope, original-target preservation, exported interfaces, configuration, evidence disclosures, attribution, and both PDF pages. Other reviewers cover the complete mathematical proof and English-to-Lean fidelity; the coordinating reviewer authenticates current CI and the verifier harness. I did not rerun Lean, the harness, or repository tests. I made no changes to the worktree or Git state.

## Target and promotion scope

The canonical page remains `matrix-inequalities-and-norms/MI-26/README.md`. Its text from `## Problem statement` through the original references and status-check discussion is byte-identical to the branch base. Difficulty, Importance, Rating rationale, and the complete ID registry are unchanged. The promotion adds formal evidence to the existing counterexample; it does not replace the original problem.

The published claim concerns the original universal inequality for complex positive-semidefinite matrices and real-valued concave functions on the nonnegative half-line with nonnegative value at zero. The displayed witness uses `f(t) = t - t²` and rank-one projections. The canonical page and manifest expressly exclude the optional stronger positive-definite variant from the seven exported results. They also distinguish the narrower class of functions nonnegative everywhere on the half-line: the witness does not refute that class. The whole-real Lean function representation and independence from its values below zero are disclosed.

Relative to this PR's base, the summary changes are the single MI-26 promotion: 6 to 7 Lean-verified and 83 to 82 Solved, with 57 Open and 71 Partially resolved retained. The RESOLVED change preserves the original result and adds the formal evidence and scope boundary. Separate expected promotions on advancing main are outside this branch-relative review.

## Public interface and configuration

The following seven exports, all in `NLA.MI26`, agree in order and membership across the canonical README, `formalization.yaml`, `comparator.json`, and `Solution.lean`. The Challenge and Solution declaration types agree after whitespace normalization, and each implementation's corresponding `_proved` declaration exists.

| Export | Published scope |
| --- | --- |
| `admissibleFunction_iff` | Scalar concavity and value-at-zero characterization |
| `functionalCalculus_eq_spectral` | Actual complex Hermitian continuous-functional-calculus operation equals the finite spectral expression; no continuity hypothesis on the function |
| `functionalCalculus_congr_nonneg` | Extension independence at PSD matrices |
| `quadratic_cfc` | Actual calculus for the witness polynomial equals `A - A²` |
| `witness_data` | Admissibility, projection/PSD facts, matrix calculations, and positive quadratic-form witness |
| `counterexample` | Failure for every pair of genuine complex unitary matrices |
| `not_subadditivityConjecture` | Negation of the original universal conjecture |

The declarations use the actual `cfc` operation, `Matrix.unitaryGroup`, and PSD order. The comparator permits only `propext`, `Classical.choice`, and `Quot.sound`, with no allowed definition holes. The recorded axiom report lists exactly these three axioms for all 15 audited declarations: eight internal declarations and seven exports.

The toolchain is `leanprover/lean4:v4.33.1`; LeanCert is pinned to `621a43d7cf21f87872392a01e874f2f1dbddc926`, and mathlib to `0df444a360eaa60ab8c11dca51a86af692955474`. All ten dependency revisions are full 40-hex Git pins over HTTPS. The Lake file is declarative TOML with Solution as default target. This PR changes no shared `tools/`, `tests/`, `.github/`, AGENTS.md, CONTRIBUTING.md, or ID registry.

## Evidence and attribution

The archived Linux receipt identifies proof revision `81176af27e570b59ba1e1a0745e28944e7d57c03` and comparator acceptance. I independently compared its 118 input hashes with this head: 116 match, including proof, definitions, interfaces, configuration and pins. Only the local project README and `formalization.yaml` differ; the current documentation explicitly identifies these subsequent publication-wrapper changes and the historical nature of the archived metadata. No inconsistency was found.

The publication links run `34713045511` and explains cache reuse, local versus Linux verification, and the denied nested-bubblewrap probe. It does not turn that probe into a general sandbox-security claim. These are reviewed disclosures, not a claim that I independently replayed CI.

The mathematical counterexample and informal proof remain credited to Matthew J. Colbrook; Lean formalization is credited to George Stepaniants. AI assistance and independent agent reviews are disclosed, with no claimed author endorsement or external human peer review. Historical informal-review limitations remain dated and distinguishable from the later formal promotion.

## Visual inspection

I rendered and inspected both pages of the canonical `problem.pdf`. Both pass: title and status fit, rational matrices and formulas are legible, all seven export descriptions fit, references and verification commands remain readable, and there is no clipping, missing glyph, overflow, or orphaned heading. The second page begins with a complete continuation paragraph before the historical result and original statement. The PDF, README and visible scope claims are consistent.
