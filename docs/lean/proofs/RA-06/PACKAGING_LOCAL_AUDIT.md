# RA-06 self-contained proof package: local audit

**Status:** local selected theorem proof and LeanCert kernel audit passed on 9 October 2026; a fresh isolated Linux Comparator receipt remains pending. The independent mathematical review of the frozen final theorem is [FINAL_INDEPENDENT_REVIEW.md](FINAL_INDEPENDENT_REVIEW.md).

The package is `randomized-and-low-rank-approximation/RA-06/lean`. Comparator selects only `NLA.RA06.target : NLA.Statements.RA06.Target` from `Solution.lean`. `Solution.lean` imports the copied `NLA.Proofs.RA06.Final` and applies `NLA.Proofs.RA06.target` directly. Its `Challenge.lean` has the single intentional replacement hole and is not imported by the solution. The frozen target has all original real-exponent, matrix, sampling, budget, success-probability, and all-vector quantifiers; no separate weakened theorem is selected.

## Source and configuration lock

| Item | SHA-256 |
| --- | --- |
| `ra06-source-lock.json` | `0e848a584c74e394ba65c41e6ffd708a47b3f11d4c636779efd7197562818d3f` |
| Copied `NLA/Statements/RA06.lean` | `865af15803905e04de1202266f5af75fc5486b8345fdba25a44052202742883d` |
| Copied `NLA/Proofs/RA06/Final.lean` | `54454fd6207fb55664d06d8c32ee9608c5089db08efa34d2d90716966c8b434c` |
| `Solution.lean` | `d2864804552dfd53e2f310d24ac2d28cbf84b1ebc8c0588f97af38caa5d64d90` |
| `Challenge.lean` | `68d3fbc81764b194392d030a0a704e04ab52fca8afb964ffa1ba27ac3d0144ac` |
| `comparator.json` | `3fab44e8c81f2f1103353b7d0985c38da673caaa1084b74e96e1ded75eafb99f` |
| `lakefile.toml` | `377be81ed389add753fecaa6dd8cbb74b2e2b50357dfb4e4577122ae2f26c247` |
| `lake-manifest.json` | `0b2f85a082aa6848c5c68b85de2f580c0d220e76a6be23b5aa39cc2027dcf7c2` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |

A byte comparison checked all 16 copied statement/proof files against the frozen `lean-statements/NLA` originals and their source-lock hashes. `tools/lean/ra06_source_lock.py` rejects missing, changed, symlinked, or extra copied files and checks the exact lock hash. Both the metadata validator and the project harness call it. The harness also requires exact Mathlib and LeanCert revisions from the Lakefile and manifest when it sees project name `NLARA06`; deleting both the lock and modules does not bypass validation. Existing 4.33.1 Comparator/LeanCert tooling and negative controls are used without a new toolchain profile.

## Local check

An isolated `.lake` build directory with only a shared package-cache symlink, excluded from Git, ran `lake build Challenge Solution` successfully (2071 jobs). The generated shared-harness selected proof audit is `/private/tmp/RA06ProofTrustAudit.lean`, SHA-256 `9dca3b9747d032a918e4755479358ab3779332e54ef4dbb3aeab2c6ee4bf690d`. `lake env lean` on that audit exited zero. Its log `/private/tmp/RA06ProofTrustAudit.log`, SHA-256 `f91637bbd9bf89f2727aab9cfca11d73d802a93ff1b4f5be51d0e1966c7a2b64`, prints only `[propext, Classical.choice, Quot.sound]` for `NLA.RA06.target`. The generated audit checks that the selected declaration is a theorem proof constant and runs `#assert_trust kernel` with LeanCert in kernel mode.

All 28 shared `tools/lean/test_*.py` unit tests passed, including six RA-06 source-lock/pin controls. `git diff --check` passed. The local host Python lacks `jsonschema`, so `validate_manifest.py` was not run locally; the Linux CI job installs its pinned requirements before that gate. Local results do not substitute for the fresh Linux Comparator run.
