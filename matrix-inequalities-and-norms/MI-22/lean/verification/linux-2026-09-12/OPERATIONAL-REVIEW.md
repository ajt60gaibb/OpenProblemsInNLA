# MI-22 independent Linux operational audit - 12 September 2026

**PASS.** The actual Linux run completed successfully. Both original artifact
ZIPs match GitHub's published digests and raw upload logs. All **177**
recorded inputs match the complete committed project tree and independently
reviewed mathematical sources. All **8** exports passed the actual Comparator,
standard-three axiom restriction and Lean default-kernel replay. Both the
standalone checker and MI-22 job exercised all required isolation and rejection
controls. No required job or step was skipped.

Reviewer: independent agent `/root/formal_review_standards`. I did not author
MI-22's statements, proof or candidate documentation and was not one of its two
final mathematical referees. I read their complete reports, the candidate
source/metadata and actual runtime logs, then checked all bound identities.
This is an operational audit, not a third complete mathematical review, human
peer review, source-author endorsement or a claim that Comparator determines
the English statement's meaning.

## Actual run and original archives

- Repository: `sgstepaniants/OpenProblemsInNLA`.
- Immutable candidate: [26f526cf8b6232af9528b30616076dc7a2c66ac6](https://github.com/sgstepaniants/OpenProblemsInNLA/commit/26f526cf8b6232af9528b30616076dc7a2c66ac6).
- [Lean run 34720684925](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34720684925)
  completed **SUCCESS**. All 7 jobs and every recorded step succeeded.
  Other problem artifacts in the same run are not independently audited here.
- Relevant jobs: selection `103625843532`, standalone checker
  `103625869047`, and [MI-22 `103625869134`](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34720684925/job/103625869134).
- Companion [permanent-ID run 34720684962](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34720684962),
  job `103625843771`, succeeded at the same commit. Its original raw log
  confirms all 217 permanent IDs and all 17 ID tests.

| Original archive | GitHub artifact ID | SHA256 matched to GitHub metadata and upload log | Extracted files |
| --- | --- | --- | --- |
| `lean-MI-22.zip` | `10306730657` | `58dff766eaa79d82b572fdc46d299fff4e9f3aafeae1a987bd61b63fb3b11ab6` | 13 |
| `lean-checker-controls.zip` | `10306635394` | `b2b6d1d1d97717a2dc70043ec1f3128c2067b38572fedd45cf5b07e7811388b0` | 10 |

The complete original `run-logs.zip` has SHA256
`95657468387afd9e2c0522d55f8b62e927e12316d98f4ef8b8c3d5350bdc903d` and contains **87** internal log files,
whose sizes and hashes are retained in [run-log-archive.json](run-log-archive.json).
It was retrieved from GitHub's authenticated run-log endpoint. Unlike the two
artifacts above, no GitHub-published digest is claimed for that log ZIP. The
full original archives, selected raw job logs, metadata and exact extracted
bytes are preserved. Archive paths, symlink exclusion and CRC integrity were
checked.

## Reviewed source and statement identity

The actual [receipt](artifacts/lean-MI-22/verify-20260912T214303Z-4163/result.json) records
`comparator-accepted`, the exact commit and all 177 input hashes. Its key set
matches the complete `git ls-tree` project inventory, and every byte matches
both the immutable Git blob and the candidate worktree. The complete source
snapshot is retained under `source/matrix-inequalities-and-norms/MI-22/lean/`; no nested evidence manifest
is omitted.

Proof-freeze SHA256 is
`f1c267a6aa600074d3b054863926d5f9cdbf6b0eadb83912a912277ac54018a0`.
All **103 non-README files of its 104 inputs** remain unchanged, and the
historical README is preserved in its candidate archive. The exact source and
configuration identities from both independent final-referee evidence sets
match all eleven central mathematical/statement/source-mapping inputs. Both
final reports bind the complete proof freeze and the actual Proof/Solution
hashes. All four report hashes also match the receipt and packaging record:

- `statement-referee-1.md`: `13556154d85fefbf81b0171bf7ff9028478b2c15327c67c78f3dc7fd18a4129a`.
- `statement-referee-2.md`: `abc0e176440936638ae20ce0b105bc823b125a3fb7eaeaf13f95ff3e14eda1f7`.
- `proof-referee-1.md`: `250b98be84248ba8dcb1c9be0a1d60743b88d0aadf5919ac6baf601a6f9597c3`.
- `proof-referee-2.md`: `b97c55e0d2667efa9b297039db26801f66af3a9cd80a8a2de39d45c1ce6a6e77`.

The current candidate README and v0.4 manifest match their independently
reviewed packaging hashes and passed the actual Linux schema/coverage check.
Their pending-Linux wording accurately records the pre-execution candidate;
this audit preserves those historical bytes. All **8 original canonical and
source files** match the reviewed upstream base
`8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc` and are separately retained. The
original target, source attribution and canonical **Solved** status were not
changed. [identity-verification.json](identity-verification.json) records the
complete checks.

## Actual fresh elaboration, Comparator and kernel replay

The trusted harness copied source without old project `.lake` outputs into a
new `nla-fresh-proof-yv2mc723/project` directory, constrained the environment,
and checked input hashes around dependency preparation and verification.
The actual main command uses systemd with `RestrictAddressFamilies=~AF_UNIX`.
All **10** dependencies were freshly cloned at their exact manifest
revisions, including LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and
Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

The official Mathlib cache decompressed **8690 files**. This was **not a
complete Mathlib source rebuild**. Actual project modules were freshly
elaborated. The graph sizes were **2723 jobs** for Challenge and
**3163 jobs** for Solution; these numbers are not counts of newly compiled
dependency sources. Challenge's eight deliberate placeholders remain in its
isolated reference environment. Solution has no warnings or admissions. All
**17** internal/public transitive axiom reports contain exactly `propext`,
`Classical.choice` and `Quot.sound`; the corresponding nine internal and eight
public explicit kernel assertions ran during those builds.

The actual config and both exported environments contain precisely:

1. `NLA.MI22.singular_values_semantics`
2. `NLA.MI22.spectral_power_semantics`
3. `NLA.MI22.euclidean_norm_bounds`
4. `NLA.MI22.witness_rational_data`
5. `NLA.MI22.witness_principal_powers`
6. `NLA.MI22.witness_operator_gap`
7. `NLA.MI22.counterexample`
8. `NLA.MI22.not_weightedLogMajorizationConjecture`

There are **no definition exceptions**. The [main Comparator log](artifacts/lean-MI-22/verify-20260912T214303Z-4163/comparator.log)
shows both actual builds, both exports, successful Lean default-kernel replay,
successful statement/definition comparison and final exit status zero.
[axiom-verification.json](axiom-verification.json) retains every printed
internal/public declaration.

The retained scalar comparison is exactly **10500 < 11000**, certified by
LeanCert in explicit kernel mode on the singleton [0,0]. The exact checked
source consumes `numerical_separation` in the strict first-singular-value
reversal, which the complete negation consumes. Both already bound mathematical
referees separately inspected its actual Boolean proof term. It certifies only
this scalar separation; matrix data, positivity, CFC roots and true norm/
singular-value semantics have their own exact Lean proofs. This operational
audit does not describe that point certificate as a numerical verification of
matrix roots or singular values.

## Exact checker sources and exercised controls

The harness, source lock, bootstrap, selftest and verify bytes match the
independently audited infrastructure at
`214c142d6bfe0f0c338808f188062acbbad0fb19`. Shared tools, workflow and CI toolchain
also match the candidate's reviewed upstream base. All **58** immutable Forsythe
source files were independently rehashed, size-checked and retained with their
licenses. The exact reviewed CI probe was reconstructed from the pinned
original and matched to the actual Linux receipt.

- Forsythe source: `8d1b0c0545a77b40245e84705aa7d273e6c81e62`.
- Source lock SHA256: `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`.
- Harness SHA256: `f81767a17973956fbe9e5765c664d4639cce15ddf8c106f70cdcb32151808c2f`.
- Derived CI probe SHA256: `31057195baf238807cacbb4126c5b07f02cec55a4e4437de5f3a755b3fada803`.
- Actual Lean: `Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)`.
- Actual Go: `go version go1.27.1 linux/amd64`.
- Linux platform: `Linux-6.17.0-1022-azure-x86_64-with-glibc2.39`.

Both jobs built actual Comparator/exporter and Landrun executables; their
receipts match, including these binary hashes:

- `.tools/comparator/.lake/build/bin/comparator`: `189e88f1a3cb68130b581905f7a5d3bde47eb0578904c0ca6fb235a53d0e8bdc`.
- `.tools/lean4export/.lake/build/bin/lean4export`: `46f6a14f0f4a364d7698229130d103b67855be42f96cc5ef93929288072f1fa1`.
- `.tools/bin/landrun`: `6531f6c9bc99313170e29c4c65bf09a414741093c587389315eb81a0a31e45d7`.

In **each** of the two control suites, I inspected the actual phases and
rejection reasons, not merely a green job summary:

- Build and export run non-root as UID 1001 with six private namespaces,
  no effective capabilities and `no_new_privs`. Host-process access/signaling,
  loopback networking and AF_UNIX socket creation are denied. Outside writes,
  truncation, creation and symlink escapes are denied. The designated build
  `.lake` write succeeds; export writing and truncation fail, and outer/export
  fixture bytes remain unchanged.
- The adversarial nested Bubblewrap executable actually runs, but **UID-map
  creation is denied before any inner write executes**. The probe's label
  does not establish that an inner write ran and was blocked.
- All four unsupported or widening sandbox-option cases reject with status two.
- The real raw-kernel controls accept the honest inductive/quotient fixture,
  reject an invalid proof term and reject changed `Quot.lift` at the quotient
  post-check after kernel replay.
- All five Comparator fixtures build and export both environments and satisfy
  their configured expected phases and exit codes. Additional admitted-proof
  and genuine native-proof fixtures are rejected after export for `sorryAx`
  and `checked._native.native_decide.ax_1_1`; their expected exit-one statuses
  are checked by the successful enclosing harness.

[audit_checks.py](audit_checks.py), [control-verification.json](control-verification.json)
and the complete original raw logs retain these checks. No general guarantee
against every possible sandbox attack is inferred from the exercised probes.

## Scope and retained evidence

This completes the execution gate for the independently reviewed complete
negative answer to the original all-dimension, complex positive-definite,
all-t-in-[0,1] singular-value log-majorization assertion. Its definition
retains every proper nonempty prefix and equality of the full products.
The adapted witness is explicitly **B = D T^8 D**, rather than Colbrook's
printed integer B. The original method remains attributed to Matthew J.
Colbrook. George Stepaniants receives formalization credit with the Department
of Computing and Mathematical Sciences, California Institute of Technology,
Pasadena, California, USA affiliation, without an email address. Verifying the
printed B or the source's 10900/10200 thresholds is not claimed.

The [outer evidence manifest](EVIDENCE-MANIFEST.json) binds **303 files**;
the retained directory contains **304 files including that manifest**.
Only that exact outer path excludes itself; all nested manifests are included.
Counts are derived from actual contents. [verify_evidence.py](verify_evidence.py)
checks exact offline inventory, sizes and hashes. The complete original run-log
ZIP and its internal inventory, both artifact ZIPs, all extracted bytes and all
submitted sources are retained.

No proof, config, pin, original source, canonical page, registry or review byte
was changed. No commit, push, PR, status promotion or repeat Linux run was made.
Current publication metadata and the independent publication review remain
separate subsequent actions.
