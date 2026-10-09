# MI-18 issue #329: external Lean verification evidence audit

Date: 2026-10-06 (UTC). Reviewer: Codex AI subagent `evidence_audit`, independently reviewing the submitted external source and evidence; this is not human peer review.

## Verdict

**Approve the verification-evidence component for `Lean verified`, conditional on the separate mathematical statement/scope audit approving full correspondence with MI-18.** The repository's `CONTRIBUTING.md` explicitly permits reviewed public verification records. The inspected external source, recorded successful builds, exact target declarations, transitive axiom reports, and immutable dependency pins meet that external-evidence route. No copy of the external Lean project into the NLA repository is needed.

This is **review of the author's published, partly cached build record**, not an independent local Lean build, sandboxed Comparator run, or fresh compilation of every dependency. The catalog must say that explicitly. The local checks performed here were source hashes, import graph, statement/definition equality, script inspection, and comparison of the logs with the reported results.

## Reviewed revision and policy

External repository: <https://github.com/KitaKen1/bapat-lal-q-permanent-lean>

Immutable revision: `4200da4fc1a132d69c23fb877795b5b72089544b` (`Add publication links and verified build records`). The inspected checkout at `/tmp/mi18-329-external` reports that HEAD and a clean tracked working tree. It contains the published evidence files, dated `2026-10-05T02:42:04.399212+00:00`. The commit timestamp is `2026-10-05T11:42:30+09:00`, approximately 26 seconds later.

Read `CONTRIBUTING.md` (Lean verification), `docs/lean/README.md`, and `docs/lean/REVIEW.md`. CONTRIBUTING distinguishes the in-repository formalization workflow from externally hosted proofs and expressly allows a public source and log to support status after review. The stronger fresh Linux Comparator workflow applies to newly added in-repository projects; this audit does not claim it occurred.

Evidence links:

- [Complete target proof, Main.lean](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/4200da4fc1a132d69c23fb877795b5b72089544b/lean/Bapat/Main.lean).
- [Counterexample and decreasing pair](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/4200da4fc1a132d69c23fb877795b5b72089544b/lean/Bapat/Counterexample.lean).
- [Dated JSON verification record](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/4200da4fc1a132d69c23fb877795b5b72089544b/lean/evidence/build_results.json).
- [Build and transitive axiom log](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/4200da4fc1a132d69c23fb877795b5b72089544b/lean/evidence/build.log).
- [Audit script](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/4200da4fc1a132d69c23fb877795b5b72089544b/lean/scripts/build_audit.py).
- [Pinned main manifest](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/4200da4fc1a132d69c23fb877795b5b72089544b/lean/lake-manifest.json).

The web fetch service could not render the two requested GitHub/raw evidence URLs (cache misses). The audit inspected their bytes in the already fetched git checkout at the exact revision, rather than relying on a rendered web summary.

## Mechanical checks performed locally

1. Recomputed SHA-256 for **all 22** source entries in `lean/evidence/build_results.json`. Every hash agrees. These cover all 20 main Lean modules, the standalone proof, and the registration stub.
2. Parsed the local import closure starting from `lean/Bapat.lean`. It includes 20 local modules. `Bapat.Main` imports `Bapat.Statement` and `Bapat.Counterexample`. Neither `FClikelean/QPermanentMonotonicity.lean` nor generated `FCStatement` occurs in that graph.
3. Independently extracted and whitespace-normalized the `qPermanentMonotonicity` signatures from the main proof, registration stub, and standalone proof: all match.
4. Independently compared the inversion-count and q-permanent definition block in `Bapat/Statement.lean` with the registration stub: byte-identical.
5. Inspected the entire audit script before deciding whether to run it. It statically scans the complete proofs for proof holes/custom axioms/native trust; compares statements, shared definitions, ordered rows, and stored certificate integers; runs both builds; compiles the registration candidate; proves a second copy of the target; compares compiled theorem types by definitional equality; and examines target transitive axioms. It writes evidence files but performs no upload/publication. **The script was not executed locally** because its Lean prerequisites were unavailable.
6. Checked command availability: no `lean`, `lake`, `elan`, `docker`, or `podman` in PATH. `~/.elan` and usual `/opt/homebrew/bin/lean`, `/usr/local/bin/lean`, and `~/.local/bin/lean` locations are absent. No local kernel build was attempted and no compiler was installed.

## Public log and allowed axioms

`build_results.json` records PASS, zero exit codes for `main_proof`, `lean4web`, `fc_statement`, and `compiled_target`, and a total elapsed time of 82.59 seconds with the explicit note “Includes dependency loading and cached modules.” The textual log independently contains corresponding successful completion and zero-exit lines.

The main log reports `Build completed successfully (8955 jobs)`. The standalone reports 8960 jobs. These are Lake job counts, **not counts of freshly compiled files**. Most local proof modules in the log say `Replayed`, so the catalog should not call this a fresh kernel reconstruction from source.

The log reports exactly `[propext, Classical.choice, Quot.sound]` for:

- `BapatLal.qPermanentMonotonicity` (both complete builds);
- `Bapat.exists_positive_definite_counterexample` (both complete builds);
- `Bapat.not_bapatMonotonicity` (both complete builds);
- `Bapat.exists_decreasing_pair` (both complete builds and compiled-target audit);
- `BapatFCValidation.qPermanentMonotonicity` (compiled-target audit).

These are **transitive** `#print axioms` reports, so no `sorryAx`, custom axiom, or extra native-evaluation trust supports those targets in the reported environment. The main arithmetic declarations `Bapat.Certificate.exact_coefficients`, `strict_margin`, and `endpoint_numerator_negative` report no axioms; their source uses `decide +kernel`. The standalone arithmetic `exact_coefficients` additionally reports `propext`, which is permitted. None of these observations independently revalidates a downloaded `.olean`; they faithfully describe the reviewed public evidence.

## Why the registration `sorry` is not a proof hole in the target

`FClikelean/QPermanentMonotonicity.lean` deliberately uses `by sorry` to present a proposed Formal Conjectures registration and external proof link. It is **not** the complete proof and is not imported by the main library.

The script copies that file to `.lake/FCStatement.lean` and compiles it with `-Dwarn.sorry=false` solely for registration linting and compiled type comparison. This compilation establishes no mathematics. The subsequent checker substitutes `import FCStatement` for `import Bapat.Statement`, renames the newly proved theorem namespace to `BapatFCValidation`, and uses the genuine counterexample proof to prove the same statement. It then compares the type of the placeholder theorem to the type of this newly proved declaration. The new theorem's own transitive axiom report excludes `sorryAx`; therefore the placeholder theorem is not used as mathematical support. This is a useful type-equality check, not the repository's sandboxed Comparator protocol.

The pinned external README's statement that the registration had not been submitted is historical. A read-only GitHub metadata check on 2026-10-06 confirmed that [Formal Conjectures PR #6857](https://github.com/google-deepmind/formal-conjectures/pull/6857), “Formalize q-permanent Conjectures 1 and 2 and record their disproofs,” was submitted by `KitaKen1` on 2026-10-05 at 03:04:04 UTC and remains open and unmerged. Its current description links a newer external proof revision; this audit remains confined to `4200da4fc1a132d69c23fb877795b5b72089544b`. Submission does not establish upstream acceptance, and acceptance is not needed for the catalog's external-evidence route. No review of the upstream PR's changed proof sources is claimed here.

## Toolchain and dependency pins

Main proof: `leanprover/lean4:v4.33.1`.

| Package | Manifest revision |
|---|---|
| formal_conjectures | `89294ea02bd7cd678d59984add52cb4baef3dbf4` |
| mathlib | `0df444a360eaa60ab8c11dca51a86af692955474` |
| plausible | `b7eb3304aeae834b12dda98993a37f6a41f6f0bb` |
| LeanSearchClient | `5f4d51b81cbd3f6b32b156bfad9056621a040404` |
| importGraph | `16f02aa7642864af59f1ff0e384a015994db9118` |
| proofwidgets | `4be2e3d5087eeb272cf5a8853b8f9dd025ef5957` |
| aesop | `3448c0bcc5ce01b2d1546e483ec3620e32df3d0e` |
| Qq | `92c15be17b7caf78c2ad767ec40f89052d908d81` |
| batteries | `4488d40d070b9700d4d5a6aa342f0d40c31b2a2d` |
| Cli | `6130a47896ce867c6a4a55373441e59e565bad0f` |

Standalone proof: `leanprover/lean4:v4.35.0-rc3`; mathlib `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`. Its manifest likewise pins all transitive dependencies to full revisions. The standalone log prints actual Lean version `4.35.0-rc3`. The main JSON version string is read from `lean-toolchain` by the script, not from a captured `lean --version`; it is the configured version rather than independent binary attestation. This is a minor evidence limitation to preserve, not a discovered proof defect.

Some manifest `inputRev` fields say `main` or `master`; the resolved `rev` fields are full immutable commit hashes. Retain the committed manifests when reproducing. Do not run an unqualified dependency update and then describe altered dependencies as the original pinned build.

## Reproduction commands for a fresh temporary clone

Requires an existing Elan installation or both configured Lean toolchains. These commands are recommended reproduction instructions; they were **not run in this audit**.

```bash
git clone https://github.com/KitaKen1/bapat-lal-q-permanent-lean.git bapat-lal-audit
cd bapat-lal-audit
git checkout --detach 4200da4fc1a132d69c23fb877795b5b72089544b
cd lean4web
lake exe cache get
cd ../lean
lake exe cache get
python3 scripts/build_audit.py
```

This prepares both dependency caches and then runs the reviewed author script. A fresh clone has no local Bapat project build artifacts, so those sources must be compiled. Cache retrieval still uses prebuilt dependencies, and must not be described as independently rebuilding every dependency from source. Confirm the two committed manifests have not changed after preparation. For only the principal theorem and its printed axiom reports, `cd lean && lake --wfail build Bapat` is the narrower check.

## Relevant hashes outside the published source-hash map

```text
99a12406cae615b50c249474191623f0e0d325a7c859334dffa05498b5ebc6cc  lean/scripts/build_audit.py
6e29e3110056bbba2f60b7997149559afa188fdb1120794eee7dcafe5d275809  lean/evidence/build.log
59bba246209193717baebe36e65f9b59741f21f8c517f3a0c21f05aaea537c28  lean/evidence/build_results.json
3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71  lean/lean-toolchain
a63ad912a03e7c43581a24026d9b7df193a0b171772693eb17869c848acd780f  lean/lakefile.toml
b6a24148ccc0139b0fdc727f1fe81afea1a69dfb16ddedb22041072396f01216  lean/lake-manifest.json
bc84812c94489d1e3e191baa1dc10d5eb684382d7fe9d2a5ab085e72c1c67e47  lean4web/lean-toolchain
6553e4baf7f11e171360386c78b8a18f30bc9fcaf3c43206eb932ccd15ed6d16  lean4web/lakefile.toml
cabff3149532db7990ff24d0fb8d3ea0f47137d30e454571960aa1cb1e79e089  lean4web/lake-manifest.json
```

## Suggested truthful canonical wording

“On 2026-10-06 this catalog reviewed the immutable proof sources and the author's successful verification record dated 2026-10-05, including transitive axiom reports for the complete target and the counterexample theorems. All 22 published source hashes match the pinned revision. The recorded Lake builds include cached modules; the catalog did not rerun Lean locally. The reported target axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.”

The formal scope is an existential non-diagonal complex Hermitian positive definite counterexample of order 144 and an actual decreasing pair on `[-1,1]`. Do not attach Lean verification to the separate fully explicit scaling `10^70 H + I` and comparison point `1 - 10^-70`: upstream expressly says those decrease claims are not formalized. Nor does this establish a real symmetric counterexample or a minimum counterexample dimension. Full mathematical correspondence remains the responsibility of the separate statement audit.
