# Independent shared statement infrastructure review

Reviewer: OpenAI Codex agent `/root/inventory` (AI), independent of infrastructure author `/root/infra_audit`.

Verdict: **APPROVE the reviewed infrastructure design and local evidence, with the execution limits below.** Phase: `infrastructure`.

The infrastructure correctly separates a closed `Prop` definition from a proof of that proposition. The declaration checker inspects elaborated declarations, requires a safe definition with type exactly `Prop`, and rejects any transitive axiom other than `propext`, `Classical.choice`, or `Quot.sound`. The Lean rejection controls cover a target axiom, a non-Prop type, a free parameter, a custom-axiom dependency, a sorry dependency, and an actual native_decide axiom. Intentional holes appear in the trusted Comparator challenge and executable rejection controls only; they are not proof evidence for a catalog target.

The numerical smoke theorem uses both the global LeanCert kernel trust option and explicit `leancert (trust := kernel)`, followed by a kernel-trust audit. Its exact rational log bound exercises infrastructure only. No artificial numerical computation is demanded merely to define a problem proposition.

The two specification and two Lean-boundary review gates require distinct disclosed AI reviewers who are not statement authors. Reports are hash-bound. Specification approvals bind the complete canonical README, exact byte-identical ORIGINAL snapshot, and numerical/mathematical specification. Boundary approvals additionally bind live and frozen sources, their repository-local import closures, and all package pin files. Missing approvals, self-review, changed reports, changed inputs, omitted imports, path escapes, symlinks, duplicate JSON keys, orphan target modules, missing snapshots, and removal of previously published statement records are rejected. Plain-import restrictions avoid silently overlooking unsupported import syntax. These are mechanical binding checks: they do not independently establish reviewer honesty, review chronology, or mathematical correspondence, which the documentation states explicitly.

The frozen boundary is a separate namespace and source file. The freeze command refuses to overwrite it. Generated checks compare the actual propositions by definitional equality. Comparator certificates prove only `Target = ReviewedTarget`; the configuration includes no definition holes and never names Target itself as a proved theorem. Shared imported semantics are held by review hashes and dependency pins; equality to a frozen proposition is not substituted for informal-to-formal review.

Lean 4.33.1, LeanCert, Mathlib, and every transitive package have committed exact revisions. The workflow uses pinned action commits, disabled credential persistence, read-only repository permission, and a separate Linux Comparator job with the existing real-isolation harness. The original proof-verification workflow and tools/lean files have no working-tree diff. The new workflow has no draft bypass, no automatic catalog promotion, and no relaxation of existing proof axioms. Inventory changes trigger CI, and inventory tests plus a check against its recorded immutable campaign base are included.

I independently ran all 13 Python rejection tests: PASS. I independently ran the published-base metadata validation on the then-empty statement scaffold: PASS for zero metadata records. That confirms scaffold validity, not coverage completion. I inspected the coordinator-produced local development receipt and all five recorded module source hashes match the reviewed bytes; all five recorded elaboration exits are zero. The kernel smoke log lists only the three permitted standard axioms. This review did not rerun Lean compilation or Linux Comparator; root's local receipt is reported as supplied evidence rather than an independently reproduced kernel run. No fresh Linux CI/Comparator success is claimed.

No blocking defect was found in this reviewed scope. The general original-problem semantics remain the responsibility of the two per-target independent reviews, and actual Linux isolation/Comparator completion must be obtained and reported separately before claiming it happened.

## Reviewed input hashes

- `tools/lean_statements/check.py`: `20bb3b83cddbfbe7e66aa0741d3d142c23d11f63ceb7a2367308223d7c4a20d2`
- `tools/lean_statements/test_check.py`: `43c4ba93595f3dfd6dd5806c2ab8ea81af51222765b0000a1c090d8c09bc6af9`
- `lean-statements/lean-toolchain`: `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71`
- `lean-statements/lakefile.toml`: `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40`
- `lean-statements/lake-manifest.json`: `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8`
- `lean-statements/NLA.lean`: `82bdcd914a1848302a373a2e86156bf4b7ea72d2a7bfd4cdeee5d07944ad3e2c`
- `lean-statements/NLA/Statements/Infrastructure.lean`: `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37`
- `lean-statements/NLA/Statements/KernelSmoke.lean`: `d2974e121f3e06ff2fb7ec220ebd026ce843db41a798e86aca3bc07c82f154fe`
- `lean-statements/StatementControls.lean`: `3c5396f5cd0d787db91f3f7f24ce2f3e8cdd47d020fd71756c4e03b5a683a8a3`
- `lean-statements/IdentityChallenge.lean`: `257f08daa52e339bd64501b1b69b3acfe6ad2a104e7754da92f8a806fb9b593c`
- `lean-statements/IdentitySolution.lean`: `b2fcad5d1ff4f28fdd35b9724d9c7a757588dde728152469fade45ab63af49a9`
- `lean-statements/comparator.json`: `7266f9044dadac89a9274c23ef1fa4487bd158e128d09cafce533acaf13996fc`
- `lean-statements/README.md`: `c6dcb1f37cb7cce6ee1a713df7299a0e3e670fb253cdfd50f73d4659a9a96785`
- `.github/workflows/lean-statements.yml`: `d16eec6b6828466482077c69de475c1d175cd2172cd38fde0331cbb6eccd1de9`
- `docs/lean/statements/README.md`: `f25fb92ea782199c0787a3c59ba224468bdf28d1dc0592da9b8bfe5954a21bdf`
