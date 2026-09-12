# PR #183 — MI-22 publication and authenticated Linux evidence

Reviewer: Codex AI agent `/root/audit_tensors_complexity`. Date: 12 September 2026.

**PASS for publication scope and actual Linux verification evidence.** This review is independent of the proof implementer. It is an informal AI audit; the complete proof implementation is separately assigned to another reviewer. No local macOS Lean execution is offered as authoritative verification.

Reviewed head: `1dddf3d17681a91adbcf1dfa43b7ee79653f55fd` in the clean read-only worktree `/tmp/nla-audit-183`. Comparison base: `f41f1f9ffa2171550d4bb795862c6170c4f26070`. No repository or remote mutation, workflow approval, or submitted-script execution was performed.

## Publication and target preservation

- MI-22 keeps its permanent path and ID. Its original statement and reference text are byte-identical from `## Problem statement` onward. Difficulty, importance, rating rationale, and all 217 registry entries are unchanged.
- The original informal `solution.md`, `solution.tex`, `solution.pdf`, Colbrook's retained original TeX, and the original independent review remain byte-identical to the published base. The new material does not overwrite the original resolution or its credits.
- Attribution consistently separates Matthew J. Colbrook's negative resolution and method from George Stepaniants's Lean formalization, with AI assistance disclosed. No external human peer review, source-author endorsement, or historical priority is asserted.
- The adapted witness is clearly disclosed in the canonical page, project guide, source correspondence, and formalization metadata: the same diagonal `A`, but a different exact rational `B=D T^8 D`, with first-prefix violation at dimension three and `t=1/8`. The new bounds are left norm above 11000 and `AB` norm below 10500. The source's integer `B`, residual-to-root lemma, and 10900/10200 bounds are explicitly retained as separate informal results rather than claimed as the formal witness.
- I read the actual Definitions, Challenge, Solution, project guide, source correspondence, Comparator config, and formalization manifest. The definitions preserve every positive dimension, complex positive-definite matrices, all real parameters in `[0,1]`, every proper singular-value prefix, and equality of the full products. The factor order in the weighted mean and product agrees with the retained target. A single valid first-prefix counterexample refutes this whole universal statement; it does not assert failure for every parameter.
- I checked the primary preprint's conventions and Conjecture 1.1 on printed pages 1–3: [Ghabries–Abbas–Mourad–Assi](https://arxiv.org/pdf/2105.13356). Its broader semidefinite conjecture contains the canonical positive-definite question. The neighboring Conjecture 1.2 is a different target.
- Exactly **eight** public names occur in Challenge, Solution, Comparator configuration, and the manifest's main results, with consistent ordering: singular-value semantics, spectral-power semantics, Euclidean norm bounds, rational data, principal powers, operator gap, counterexample, and full negation. `definition_names` is empty. The only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- The default Lake target remains Challenge, while the documented full-proof command explicitly builds Solution. Intentional Challenge placeholders are disclosed. Solution imports Proof rather than Challenge. LeanCert's stated role is only the kernel-certified scalar separation `10500<11000`; the publication does not claim interval certification of the matrix roots or singular values.
- The diff is confined to MI-22 and intended root/category summaries. Shared workflows, tools, tests, documentation safeguards, and the permanent registry are unchanged.

Using the PDF skill's render-and-inspect procedure, I displayed and inspected **both canonical problem PDF pages**. Status, credits, witness distinction, all eight declarations, original statement, references, and reproduction commands are readable. No clipped equations, overflow, missing glyphs, or orphaned heading was found. The unchanged longer informal solution PDF was preserved, not newly re-audited visually in this bounded task.

## Independently authenticated current Linux run

I queried GitHub directly and retained the run metadata and raw log for [upstream run 34722926772](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/34722926772). It completed successfully for exact PR head `1dddf3d17681a91adbcf1dfa43b7ee79653f55fd`.

The artifact receipt records checked commit `112ff43fdc43aab1e5f9c3dad783daa6ecaa2c26`. The separately downloaded GitHub commit object confirms its two parents are exactly:

1. Published base `f41f1f9ffa2171550d4bb795862c6170c4f26070`.
2. Reviewed PR head `1dddf3d17681a91adbcf1dfa43b7ee79653f55fd`.

Artifact `lean-MI-22`, GitHub artifact ID `10306913199`, was downloaded as its original ZIP. Its SHA-256 matches GitHub's authenticated artifact digest: `b54068a65310089905f67d01b0b65c2a5d66e907b314a37e677850ced1ae01b0`.

The current receipt contains **513 project input hashes**. I compared every hash to the reviewed project and confirmed that the key set is exactly the complete tracked project file set: all 513 match, with no omitted or extra tracked input. This current run includes the added archival evidence and current documentation; the publication's historical count of 177 belongs to the explicitly named earlier fork run and is not the current receipt count.

The current Comparator log freshly builds the actual project modules, exports both environments, accepts all eight configured declarations, and explicitly reports **“Lean default kernel accepts the solution”** followed by acceptance. All **17 internal/public axiom reports** in that actual log contain exactly the standard three axioms, including every configured public theorem and the scalar separation. No definition exception or admitted/native trust is accepted.

The checked source lock is SHA-256 `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`, matching both receipt fields and the unchanged published file. It pins tool sources to Forsythe commit `8d1b0c0545a77b40245e84705aa7d273e6c81e62`. The actual tool receipt reports Lean 4.33.1 on `x86_64-unknown-linux-gnu`, with executable digests and Linux platform identification. The unchanged harness verifies these sources, executable identities, and project input preservation before issuing its acceptance receipt.

Actual per-project controls passed: both build/export sandbox modes; four invalid-option rejections; three default-kernel/quotient replay controls; five Comparator regressions; and rejection of both an admitted proof and a native-decide axiom. The standalone `checker-controls` job was correctly skipped because shared tools were unchanged. Its absence is not substituted for control execution: all these controls ran inside the MI-22 verification job and are present in the downloaded logs.

The dependency log shows fresh clones/checkouts of all ten exact manifest revisions, including Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. The official Mathlib cache decompressed 8,690 files. This supports fresh project elaboration with pinned dependencies, not a complete source rebuild of Mathlib.

## Retained independent evidence and limits

Evidence directory: `/tmp/nla-pr-183-ci`. It contains the original artifact ZIP, authenticated run/artifact/commit JSON, raw GitHub log, extracted operational logs, and `independent-authentication.json`. The independent `authenticate.py` uses only standard-library file reads, hashes, regular-expression checks, and read-only git queries; its assertions passed. It did not execute submitted proof or review scripts.

This report authenticates the **new upstream run** and its exact reviewed input correspondence. Historical fork receipts remain archived source evidence; acceptance here does not depend on treating a supplied historical PASS statement as authority. Human-to-formal mathematical fidelity and implementation correctness require the separate proof review, while the checked definitions and publication scope present no blocker within this bounded audit.
