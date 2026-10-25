# RA-05 combined support package: independent assembly review

**PASS for the frozen eleven-export support package, 23 October 2026.** Reviewer: independent Codex agent `/root/proof_route`. Inspected package: `/private/tmp/nla-ra05-oct23-package`. This review covers root's minimum-support proof and the combined assembly, declarations, frozen statement, source reuse, metadata and reproduction setup. I authored the separate hyperplane proof and do **not** count this report as an independent mathematical review of that proof. Its independent review is `/root/inventory`'s retained `FINAL_REVIEW_INVENTORY.md`.

RA-05 remains **Solved**. Neither the full `Classification ∧ NegativeAnswer` nor any all-exponent joint rate bound is proved by this package. This review is AI-agent review, not external human peer review.

## Exact reviewed snapshot

`PACKAGE_LOCK.json` SHA-256: `1a74a51de1768aa37710dce52bd6100ac2091dbee32c4e03cee43acb8be9cdef`.

The complete independent 36-file input snapshot is recorded in `package-review-route-evidence/result.json`. Every package-lock entry matched its actual bytes; the entire snapshot was unchanged during the final source replay. Its source base is published `5487945e5a72abd952b0c89915915de8cc9b3e65`.

Selected assembly hashes:

| File | SHA-256 |
| --- | --- |
| `Challenge.lean` | `7a311a87ee64b231a1ba27b744cf0cebc7b2b96632822db2e43784a7a124a622` |
| `Solution.lean` | `1c9c8965d18bfe982bf1fb73bbd308f76a6fda551887a07e559acee03860c20b` |
| `Identity.lean` | `627477b5f8f80099f19ba234bc6c0e9808e7fe599baf5bc30dac072c8d81f770` |
| `SupportAudit.lean` | `d75ac87c8671750c16f573f87c1555cacb7c74365efd070313348f525579aaa9` |
| `comparator.json` | `eaba2868d810c22b1222dbe85ebe1d24f9ba8031f850717acf11ba4b4288d94e` |
| `formalization.yaml` | `acf6121b4c21d4cafd206ca65f0371a7711a5398b0b477e862e06d1141a6a8f4` |
| `reproduce.py` | `69991017dd73c365fa827ecbc01d466908615ae6605fa482b149146716c54eec` |
| `lakefile.toml` | `b054f97e5476750dd0a3a25c39de09a295086e5f96fe9ac3fd931cefc0108e80` |
| `lake-manifest.json` | `b92de333f75f69ea9b5cf2033f5f2a2e763d349c17fe97312c1c5fbed815cdda` |
| `SupportMinimum.lean` | `d21474d121f82481cf7de107ecaa8405d0b2d12cf60c08ef75fcbea471c1f0ce` |

## Independent mathematical and semantic checks

Root's `SupportMinimum` correctly proves eight lemmas on the actual frozen definitions. A row cost is nonnegative for every real exponent because its base is a nonnegative square root. Nonnegativity survives the finite sum. Therefore unit weights satisfy both approximation bounds for every nonnegative accuracy, without an input-rank or dimension restriction. Their support is exactly the row count. The natural-number feasible-budget set is nonempty under that same accuracy condition, so its infimum belongs to it. Combining this membership with the lower-bound property of the infimum produces a coreset whose actual support is exactly `MinimumSupport`. The per-matrix minimum is included in the actual ENNReal supremum whenever `k<d`; completeness of ENNReal requires no finite-supremum hypothesis. Empty row sets are included. No statement silently assumes the asymptotic classification.

The combined `Challenge` has exactly eleven named reference declarations. Every selected theorem header agrees literally with its implementation, modulo whitespace. Its namespaces, implicit dimension variables and hypotheses match. `Solution` imports only `SupportMinimum` and `HyperplaneBridge`, both of whose transitive imports exclude `Challenge`. No new axiom, admitted proof or native decision shortcut is used. Comparator names exactly these eleven distinct exports, supplies no replaceable definition names, and permits precisely the three foundational axioms. It does not select or claim the unproved full Target.

All eight exact source identity checks passed against the published base: live RA05, live RA06, statement infrastructure, frozen `Reviewed/RA05`, canonical RA-05 original, numerical specification and both credited source manuscripts. `Identity.lean` independently compiled its `rfl` equality between the live and frozen full Targets. Originals, ID and path are preserved. The cited Hyperplane tests lemma occurs in source Part I, and its residual/homogeneity deduction matches the advertised bridge. Sidney Holden and the imported upper-bound/Fourier antecedents retain mathematical credit; formalization and AI-agent review are described separately.

## Fresh independent mechanical checks

`package_review_route.py` rebuilt all eleven local source modules with isolated temporary NLA objects using official Lean 4.33.1 and the materialized dependency cache. `Challenge`, `Solution`, `Identity` and `SupportAudit` all compiled successfully. Every one of the eleven `#assert_trust kernel` checks passed. Every corresponding `#print axioms` returned exactly `propext`, `Classical.choice`, `Quot.sound`. Raw logs, commands, exact source hashes, byte-identity checks and final immutability checks are in `package-review-route-evidence/result.json` and the adjoining logs. All ten dependency Git revisions match the manifest and all tracked package sources are clean; independent details are in `dependency-checks.json`.

The first replay's source checks also all passed, but its integrity flag correctly rejected a stage that root was still updating with the manifest-name correction, `reproduce.py` and review files. That diagnostic is retained as `attempt-before-freeze.json`. The final frozen replay passed every check. This was a snapshot-integrity correction, not a Lean proof repair.

I independently parsed the actual Lake TOML in a disposable directory with `lake check-build` and `lake translate-config lean`; both exited zero. The resulting config has the correct `NLARA05Support` package name, pinned LeanCert dependency, the actual NLA/Reviewed library globs and all three advertised default libraries: Solution, SupportAudit, Identity. The manifest root name matches. The translated config and command logs are retained. This validates configuration parsing and target declaration; it is not advertised as a full materialized `lake build` run.

`reproduce.py` was inspected: it checks pinned Lean version, package source hashes and all dependency revisions/cleanliness, compiles the actual eleven-module sequence into a temporary directory, checks each source's immutability, removes the temporary objects and repeats dependency checks. Its result explicitly denies Linux isolation, Comparator execution and a separate raw-kernel replay. Its scope is accurate. The documented Lake and Linux commands name actual files and targets.

## Metadata and limits

The README and `formalization.yaml` consistently describe support only, retain canonical Solved status, set `whole_problem_verified:false`, identify all eleven exports, distinguish intentional Challenge holes from completed proofs, and state that isolated Linux verification is pending. No finite diagnostic or sampler-specific impossibility is substituted for an arbitrary-weight coreset classification. The local evidence supports those statements.

No blocking defect was found. Actual isolated Linux Comparator, raw-kernel and rejection-control receipts remain separate required checks of the committed source. This report does not certify those unexecuted checks, a completed RA-05 proof, or later modifications outside the bound snapshot.
