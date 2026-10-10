# RA-06 independent Comparator-package review

**Reviewer:** `/root/ra06_sampling_review`, 9 October 2026. **Verdict:** APPROVE the frozen self-contained package and local selected-Solution LeanCert kernel check. This is not an isolated Linux Comparator receipt; that CI gate remains pending. The [independent final mathematical review](FINAL_INDEPENDENT_REVIEW.md) separately approves the proof of the exact frozen target.

`problem_ids.json` still maps `RA-06` to `randomized-and-low-rank-approximation/RA-06/README.md`. The package's `comparator.json` selects exactly `NLA.RA06.target`, and `Solution.lean` proves it with the literal type `NLA.Statements.RA06.Target` by applying the frozen `NLA.Proofs.RA06.target`. The separate `Challenge.lean` gives Comparator the same target type with its one intentional `sorry`; it is not imported by `Solution.lean`. No alternate statement, restricted exponent or matrix family, or weakened numerical claim is selected. The package manifest advertises exactly this theorem and accurately records that Linux verification is pending.

I independently traversed the local imports from `NLA.Proofs.RA06.Final`: the reachable `NLA` closure is **exactly 16 files**, with no missing or extra module. Every copied byte matches `lean-statements/NLA` and its entry in `ra06-source-lock.json`; in particular the statement and final proof retain the hashes from the earlier mathematical review. `tools/lean/ra06_source_lock.py` fixes the whole lock digest and final proof hash, requires exactly 16 ordinary files, and rejects changed, missing, symlinked, or extra copied sources. Both the metadata validator for the canonical RA-06 project path and the harness for the package name `NLARA06` invoke that validator. The harness still catches a missing lock when the copied module tree is deleted. A proof-source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` in the copied `NLA` proof closure or `Solution.lean`; the only build warning for `sorry` is the intentionally isolated Challenge placeholder.

The package uses the existing Lean 4.33.1 verifier profile. Both Lakefile and manifest pin Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert at `621a43d7cf21f87872392a01e874f2f1dbddc926`; the RA-06 harness check requires the exact Mathlib URL/revision/inputRev and a present reviewed LeanCert pin before comparison. Other manifest Git dependencies have resolved commit hashes and HTTPS GitHub URLs. The workflow selects this registered project through `tools/lean/projects.py`, uses the default profile, installs metadata-validator requirements, and then runs the shared Linux bootstrap and verifier. That verifier checks the committed fresh snapshot, runs the existing sandbox and negative controls, invokes Comparator before building the Solution, and generates a LeanCert kernel audit of the selected theorem proof constant.

I ran `harness.validate_project(project, "default")`, `harness.pinned_leancert(project, "default")`, all **28** local verifier unit tests, and `lake build Challenge Solution`; each passed. I also created a fresh independent audit that imports `Solution`, elaborates `example : NLA.Statements.RA06.Target := NLA.RA06.target`, requires `.thmInfo` for the selected constant, and runs `#assert_trust kernel` under `leancert.trust "kernel"`. It passed and printed exactly `[propext, Classical.choice, Quot.sound]` as transitive axioms. The author's generated shared-harness audit of the same selected theorem also passed. `git diff --check` passed. Local Python lacks `jsonschema`, so I did not independently execute `validate_manifest.py`; CI installs its requirements before that step. No fresh isolated Linux Comparator run has been observed.

## SHA-256 of reviewed inputs

| Input | SHA-256 |
| --- | --- |
| Canonical `RA-06/README.md` | `5ee10eb6d467ef6ebbd56955cdc95b2a1ff0613231d7e5ed6814679491d78f98` |
| `lean/ra06-source-lock.json` (all 16 copied files) | `0e848a584c74e394ba65c41e6ffd708a47b3f11d4c636779efd7197562818d3f` |
| Copied `NLA/Statements/RA06.lean` | `865af15803905e04de1202266f5af75fc5486b8345fdba25a44052202742883d` |
| Copied `NLA/Proofs/RA06/Final.lean` | `54454fd6207fb55664d06d8c32ee9608c5089db08efa34d2d90716966c8b434c` |
| `lean/Solution.lean` | `d2864804552dfd53e2f310d24ac2d28cbf84b1ebc8c0588f97af38caa5d64d90` |
| `lean/Challenge.lean` | `68d3fbc81764b194392d030a0a704e04ab52fca8afb964ffa1ba27ac3d0144ac` |
| `lean/comparator.json` | `3fab44e8c81f2f1103353b7d0985c38da673caaa1084b74e96e1ded75eafb99f` |
| `lean/formalization.yaml` | `399cf914ac6da0d662a692e30ac887cfe7046db9f47417f44280b19928a8464b` |
| `lean/lakefile.toml` | `377be81ed389add753fecaa6dd8cbb74b2e2b50357dfb4e4577122ae2f26c247` |
| `lean/lake-manifest.json` | `0b2f85a082aa6848c5c68b85de2f580c0d220e76a6be23b5aa39cc2027dcf7c2` |
| `lean/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `tools/lean/ra06_source_lock.py` | `0ae83f8ddd0eb26903823f21562f35d28f312eb14cc28fbfe081040b743750bc` |
| `tools/lean/test_ra06_source_lock.py` | `7bf556aa8a90eeb65c30fb0a5ceb50dc2f72eb0514981473c04b504e6582fede` |
| `tools/lean/harness.py` | `5d61855d353a2a65c24dc1b42263666a877f19261376615380c59a1cdcffb0b0` |
| `tools/lean/validate_manifest.py` | `bd36e93ce6c4026935a1cb921b1d6722eeb3d09975756a7f77f2f74b27f10677` |
| `.github/workflows/lean-verification.yml` | `850fd6f1155f62b3ad0a9636e0613b0bc2c20f81efe60424ad01f3f89053b453` |
| Independent `/private/tmp/ra06-package-independent-audit.lean` | `b78b69a37923ae2f788753cd6b3c1b77300eaa9f5c47dff53312a96707b3532e` |

Any changes to these bytes require renewed review of the affected packaging claim. The remaining authoritative evidence is a passing Linux Comparator and generated LeanCert receipt for this exact committed package.
