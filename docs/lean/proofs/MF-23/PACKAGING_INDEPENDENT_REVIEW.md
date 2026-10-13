# MF-23 independent packaging and verification-profile review

**Reviewer:** `/root/ra06_sampling_review`, 9 October 2026. **Verdict:** APPROVE the source-locked project packaging and the local LeanCert kernel audit of the exact selected theorem. The repository's isolated Linux Comparator run under the new Lean 4.34.1 profile remains **unverified**; this report is not a Comparator acceptance receipt. The separate [canonical proof review](CANONICAL_BRIDGE_INDEPENDENT_REVIEW.md) covers mathematical fidelity.

## Reviewed target and immutable inputs

The permanent `problem_ids.json` entry still maps `MF-23` to `matrix-functions-and-stability/MF-23/README.md`. `comparator.json` selects exactly `NLA.MF23.canonical_crouzeix`; `Solution.lean` exports that theorem as `NLA.MF23.Target`. Its `Challenge.lean` counterpart has the same target type and an intentional isolated `sorry`; `Solution.lean` does not import `Challenge.lean`. `formalization.yaml` names the same single result, reports the source-locked upstream proof and local bridge, and correctly says that whole-problem Linux verification is pending. The source scan of all copied `OAI` modules, `CanonicalStatement.lean`, `CanonicalBridge.lean`, and `Solution.lean` found no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` token.

I compared the 41 `OAI.Analysis.DirectCrouzeix` files byte for byte with the clean upstream checkout `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`, whose direct-proof tree is `5374ca34f6707460b2d2a3eb98b1ae7af6ea25ff`. Independently traversing `import` statements from `CompleteBound.lean` reached **exactly** those 41 files, with no missing or extra direct-proof module. The closure has only `Mathlib` as an external import. `upstream-source-lock.json` gives every module SHA-256; `upstream_source_lock.py` fixes the lock digest, provenance, exact module set, each file digest, and Apache license digest. The validator is called unconditionally for the `mf23` harness profile, including if both the lock and module directory are deleted. The metadata validator also calls it for the MF-23 project path.

The Lakefile and manifest pin Lean 4.34.1, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, and LeanCert `7f91b6eb3567437f6cfac03ed279706603ee22f4`. The profile now checks exact Mathlib URL, `rev`, and `inputRev` in the manifest, exact Mathlib URL and `rev` in the Lakefile, and exact LeanCert URL and revision in both; missing LeanCert fails. Every other manifest dependency has a resolved 40-character commit and HTTPS GitHub URL. The profile adapts exactly three SHA-checked locked toolchain text files from the Forsythe verifier to Lean 4.34.1; all Comparator, lean4export, landrun, and control sources retain their original locked hashes. Its bootstrap receipt records profile and binary digests. Its verifier retains fresh committed-source snapshotting, unprivileged Linux isolation and rejection controls, Comparator before any Solution build, and a generated `LeanCert` kernel audit of the selected `.thmInfo` proof constant.

## Checks performed

- `harness.validate_project(project, "mf23")` passed and returned the one selected theorem with only the three permitted standard axioms. `harness.pinned_leancert(project, "mf23")` returned true.
- All **22** local `tools/lean/test_*.py` tests passed, including negative tests for changed/missing/extra upstream files, missing source lock, changed Mathlib pins, changed LeanCert pins, and altered checker/toolchain bytes.
- A direct Lean 4.34.1 elaboration of `CanonicalBridgeAudit.lean` and an independent selected-Solution LeanCert audit both exited zero in the self-contained project. `#assert_trust kernel` passed for upstream `complete_crouzeix`, local `canonical_crouzeix_proved`, and selected `canonical_crouzeix`. Their transitive axiom printouts were exactly `[propext, Classical.choice, Quot.sound]`. The author's `lake build Challenge Solution` covered 8,970 jobs; this reviewer independently reran the two direct kernel audits.
- The workflow selects `--profile mf23` only for `matrix-functions-and-stability/MF-23/lean`, installs the manifest validator dependencies, and runs bootstrap and verify on Ubuntu 24.04. Project discovery derives this path from the unchanged ID registry, and changes in the project or shared verifier select it for CI.

The authoritative Linux run has **not** occurred in this review. Thus compatibility of the pinned Forsythe Comparator and its checker controls with Lean 4.34.1, the actual sandbox behavior, and a fresh Comparator acceptance receipt remain concrete integration risks. The local host lacks the `jsonschema` dependency, so I did not independently run `validate_manifest.py`; CI installs its pinned requirements before that gate. These limits do not affect the local kernel proof check above.

## SHA-256 of reviewed inputs

| Input | SHA-256 |
| --- | --- |
| Canonical `MF-23/README.md` | `ce65d34a504156e52e9b917419b7f3a0bf605cea219a4b627197de470ffbe324` |
| `CanonicalStatement.lean` | `9ce2eff57267fcccf4b6bf39c06754d65f8d4bf19316254cfa2a7372bfc11f81` |
| `CanonicalBridge.lean` | `94b52a868ff9c57afb248f410398bfe66acc9748c9633573f5f4946dab1ab4ef` |
| `CanonicalBridgeAudit.lean` | `4e19c5f4bd6982606f05532e2e7810ad6642288fbd439a3a140e4b43696ff34b` |
| `Challenge.lean` | `3540e233782f93d328b573b0cf0f16e2275319923583436efd26126c953553c2` |
| `Solution.lean` | `a55feede620de4096686ce3aae568024b9ac18e6615b1e04646cb5e20f897f68` |
| `comparator.json` | `ff8888a92bc53c34ad2030fff72d4b073365ed8c53b2dbf008737066784b6f11` |
| `formalization.yaml` | `d24773421bf8a7faef264ed98707030cbf9228e89b1926616fdb09835899ab55` |
| `lakefile.toml` | `4be61d779ae047665f2c3624f01545b9b41f66c491aa31e9a5a544e5db36ba34` |
| `lake-manifest.json` | `3a0ddbe1d5555f30725305592d35279636102a25fb0055014adcb284cc826185` |
| `lean-toolchain` | `d5edba4e4b8faad9c1baeadb265716d20d03be4d1a2647dc5e35b0c0325bea7b` |
| `upstream-source-lock.json` (all 41 module hashes) | `debce830554cb3f83e1fd7066324655bada786f1c5f7291a8aa11794ab60d511` |
| `UPSTREAM-LICENSE.txt` | `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4` |
| `tools/lean/upstream_source_lock.py` | `bb2aa9e2f4331c4412829a4f2bf61c112ce465b51896e73c2bbf74e6c8387894` |
| `tools/lean/test_upstream_source_lock.py` | `35d6b5cba289ac1f82fee9010285d99e0a8fe1491b1c10a13bb84ac930d36287` |
| `tools/lean/harness.py` | `1f459cd5e271f5a7e703f3f835bd667f6b479e3b96efc125662a079ec089b720` |
| `tools/lean/test_mf23_profile.py` | `6d1c6436e80e69c3c6ef2e16f3c011b25d51cdc4dc21f384c3c9895c00c6982d` |
| `.github/workflows/lean-verification.yml` | `850fd6f1155f62b3ad0a9636e0613b0bc2c20f81efe60424ad01f3f89053b453` |

Any change to these bytes requires a fresh review of the affected claim. The required next evidence is a passing Linux MF-23 Comparator/LeanCert receipt from this profile.
