# PR93 final provenance delta review

**PASS at latest head `387e68814c3f68ca0bfc09dabfc3fea5a97c64c2`, including the earlier `d9e25009e3ce65cf864002354830bdcc286f7252` review. No content blocker.** Compared with published main `1f22006bdaa4659fcaa0bb775a887685cd3cc566`.

All six canonical RA-12 files—README, problem TeX/PDF and solution Markdown/TeX/PDF—are byte-identical to published main. The frozen candidate proof, original target copy, independent/packaging reviews and existing verification manifests are likewise unchanged. No mathematical re-review or PDF rerender is required for this delta.

At the initially reviewed d9e2500 head, the only remaining RA-12 changes were four provenance files: an appended submission-README section, the dated integration Markdown and JSON, and `verification/verify_main_integration.py`. The original README is preserved as an exact prefix. The append describes a historical integration with accepted main 87366c6, rather than claiming to represent current catalog totals or final CI.

Checked that the initially reviewed d9e2500 head is an ordinary merge whose two parents are exactly the recorded preceding submission `c797aee814c8bebe4452329c93f5d84fd9c41f1f` and incoming main `87366c62d3b5c47d170f747b1cb40ab38d501013`. The new records accurately distinguish immutable proof evidence, regenerated indexes and the combined resolution list. They preserve George Stepaniants's attribution and do not introduce a different canonical target or an additional resolution.

Read the complete new verifier before executing it: it only reads local files and Git objects, validates hashes/paths, and prints results; it does not rebuild artifacts, use the network, or mutate repository state. To avoid treating historical fingerprints as current-main checks, ran it in a separately cloned, detached checkout of the exact d9e2500 head. It passes for all ten unchanged protected artifacts, the original README prefix, 202 incoming canonical pages, 1260 incoming proof/evidence blobs, all 203 historical ID/path pairs, and the recorded integration fingerprints. The JSON's eleven protected submission files include the README whose prefix is preserved, explaining the verifier's ten unchanged-file count.

The old test/validation transcript is explicitly a dated record; its historical 203-entry totals are not asserted to be current. Current-main preservation, all 217 IDs, index regeneration and a fresh required CI run remain the integrating agent's checks. This review does not convert the prior workflow failure into a passing result.

Evidence: `PR93-final-delta-evidence.json`. Historical verifier checkout: `/private/tmp/nla-review-tensors/PR93-dated-scratch`. No user/shared worktree, remote branch or published record was changed by this review.

## Author's two subsequent main integrations — checked 12 September 2026

The latest head adds exactly seven RA-12 provenance changes beyond d9e2500: another README append, two dated Markdown/JSON records, and two read-only verifiers. All six RA-12 canonical/problem/proof artifacts remain byte-identical to published main 1f22006. The older README remains an exact prefix, and earlier proof evidence and historical checker files are preserved.

Verified the ordinary merge parents directly:

- `5b191a7318f29c418fa2920daff860ecbc501d35` joins d9e2500 and incoming `bfaa1d0675f24011e42740d48ea6966f83bb1bff`.
- `387e68814c3f68ca0bfc09dabfc3fea5a97c64c2` joins 5b191a7 and incoming `9a697fdebee32be3003117700423bb81b1aab963`.

Read both new verifier sources before executing them. They read files and Git objects, handle symlink blobs explicitly, validate fingerprints and report results without edits or network calls. Ran each in its own exact historical checkout using the isolated scratch clone. Both pass:

- bfaa1d0 integration: 17 protected submission paths; 2,193 accepted incoming blobs exact plus the retained README prefix; all 217 canonical pages/IDs preserved; all fourteen previously appended upstream IDs retained; current fingerprints match.
- 9a697fd integration: 20 protected submission paths; 2,226 incoming blobs exact plus the retained README prefix; all 217 canonical pages/IDs preserved; no additional IDs. The recorded 76 Solved, 66 Open, 74 Partially resolved and 1 Lean verified counts reproduce exactly. RA-12 remains Solved, while IE-01 retains its incoming Lean verified status; no formal-verification claim is added for RA-12.

The bfaa1d0 record's action_required workflow observation is explicitly dated at 2026-09-12 00:24 UTC. The later record calls it historical and expressly makes no new current workflow-status claim. It is therefore not contradicted by the workflow's subsequent approval/execution and failure on an outdated ID registry. The final integration still requires its own successful check. No historical workflow result is relabeled as current or passing.

The seven additions accurately describe provenance-only ordinary merges, accepted mathematical scope and preserved attribution. They add no proof premise, target, status promotion or claim of PDF rebuilding. No correction requested.
