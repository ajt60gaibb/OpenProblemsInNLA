# MI-03 independent Linux operational audit - 12 September 2026

**PASS.** The actual Linux run completed successfully. Both original artifact
ZIPs match GitHub's published digests and raw upload logs. All **173**
recorded inputs match the complete committed project tree and independently
reviewed mathematical sources. All **8** exports passed the actual Comparator,
standard-three axiom restriction and Lean default-kernel replay. Both the
standalone checker and MI-03 job exercised all required isolation and rejection
controls. No required job or step was skipped.

Reviewer: independent agent `/root/formal_review_standards`. I did not author
MI-03's mathematical statements, proof or current candidate documentation.
I was its independent statement referee 1 and final proof referee 1, and this
separate audit checks actual Linux execution and source identity. I read the
candidate guide, manifest, both final reports and actual runtime logs, then
checked all bound identities. This is not human peer review, source-author
endorsement or a claim that Comparator determines the English statement's meaning.

## Actual run and original archives

- Repository: `sgstepaniants/OpenProblemsInNLA`.
- Immutable candidate: [901ba5ffad3b57557b60c7360df67659d8b8aa21](https://github.com/sgstepaniants/OpenProblemsInNLA/commit/901ba5ffad3b57557b60c7360df67659d8b8aa21).
- [Lean run 34722618003](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34722618003)
  completed **SUCCESS**. All 12 jobs and every recorded step succeeded.
  Other problem artifacts in the same run are not independently audited here.
- Relevant jobs: selection `103631122518`, standalone checker
  `103631153252`, and [MI-03 `103631153359`](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34722618003/job/103631153359).
- Companion [permanent-ID run 34722618004](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34722618004),
  job `103631122512`, succeeded at the same commit. Its original raw log
  confirms all 217 permanent IDs and all 17 ID tests.

| Original archive | GitHub artifact ID | SHA256 matched to GitHub metadata and upload log | Extracted files |
| --- | --- | --- | --- |
| `lean-checker-controls.zip` | `10306627955` | `55dd2ca9c189c2b5fda8d8785cbf0177a74f77cdc26d0f12f03a3c4c11526f8d` | 10 |
| `lean-MI-03.zip` | `10306413755` | `ca9ae612e2b9daef185d7d23fcfe2930c6a73b3cdbefa2b77bb24108ffc74e8d` | 13 |

The complete original `run-logs.zip` has SHA256
`0995ed6125ea901dcaa61e1d7c161327ff6a6ae01222ab39456df2a454061cbb` and contains **152** internal log files,
whose sizes and hashes are retained in [run-log-archive.json](run-log-archive.json).
It was retrieved from GitHub's authenticated run-log endpoint. Unlike the two
artifacts above, no GitHub-published digest is claimed for that log ZIP. The
full original archives, selected raw job logs, metadata and exact extracted
bytes are preserved. Archive paths, symlink exclusion and CRC integrity were
checked.

## Reviewed source and statement identity

The actual [receipt](artifacts/lean-MI-03/verify-20260912T222447Z-4133/result.json) records
`comparator-accepted`, the exact commit and all 173 input hashes. Its key set
matches the complete `git ls-tree` project inventory, and every byte matches
both the immutable Git blob and the candidate worktree. The complete source
snapshot is retained under `source/matrix-inequalities-and-norms/MI-03/lean/`; no nested evidence manifest
is omitted.

Proof-freeze SHA256 is
`fcff9e256a6425853b15def24260b419613a72d9122c0a5bedea4b4cd5f0fd1d`.
All **100 non-README files of its 101 inputs** remain unchanged, and the
historical README is preserved in its candidate archive. The exact source and
configuration identities from both independent final-referee evidence sets
match all eleven central mathematical/statement/source-mapping inputs. Both
final reports bind the complete proof freeze and the actual Proof/Solution
hashes. All four report hashes also match the receipt and packaging record:

- `statement-referee-1.md`: `2a46c81ee78c4d0718c862cecf76a20425447c3ba502a78a477caf8a30e20de2`.
- `statement-referee-2.md`: `47c4a7ada59afabcbf5657da3cdc31598db49c88e2beed7b7b50f5b0dde09ce0`.
- `proof-referee-1.md`: `7a00100cd2070c759b0dc71c743f9d58428c2ae5bfe41ffda4696efd4003391f`.
- `proof-referee-2.md`: `129c3b352346d1da8a192a0f4d662eb0a6e9b9f5a7a02b7efc176f2a7a051ba3`.

The current candidate README and v0.4 manifest match their reviewed packaging hashes and passed the actual Linux schema/coverage check.
Their pending-Linux wording accurately records the pre-execution candidate;
this audit preserves those historical bytes. All **8 original canonical and
source files** match the reviewed upstream base
`c0601d8825e9f9e744212c62e6a43fefc1c60a22` and are separately retained. The
original target, source attribution and canonical **Solved** status were not
changed. [identity-verification.json](identity-verification.json) records the
complete checks.

## Actual fresh elaboration, Comparator and kernel replay

The trusted harness copied source without old project `.lake` outputs into a
new `/home/runner/work/_temp/nla-lean-tools/.verification-tmp/nla-fresh-proof-e604ri06/project` directory, constrained the environment,
and checked input hashes around dependency preparation and verification.
The actual main command uses systemd with `RestrictAddressFamilies=~AF_UNIX`.
All **10** dependencies were freshly cloned at their exact manifest
revisions, including LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and
Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

The official Mathlib cache decompressed **8690 files**. This was **not a
complete Mathlib source rebuild**. Actual project modules were freshly
elaborated. The graph sizes were **2714 jobs** for Challenge and
**3041 jobs** for Solution; these numbers are not counts of newly compiled
dependency sources. Challenge's eight deliberate placeholders remain in its
isolated reference environment. Solution has no warnings or admissions. All
**16** internal/public transitive axiom reports contain exactly `propext`,
`Classical.choice` and `Quot.sound`; the corresponding eight internal and eight
public explicit kernel assertions ran during those builds.

The selected theorem names in the actual config and both exports are precisely:

1. `NLA.MI03.modulus_semantics`
2. `NLA.MI03.contraction_modulus`
3. `NLA.MI03.positive_decomposition`
4. `NLA.MI03.universal_upper_bound`
5. `NLA.MI03.root_of_unity_data`
6. `NLA.MI03.sharpness_witness`
7. `NLA.MI03.sharp_constant`
8. `NLA.MI03.odd_contraction_conjecture`

There are **no definition exceptions**. The [main Comparator log](artifacts/lean-MI-03/verify-20260912T222447Z-4133/comparator.log)
shows both actual builds, both exports, successful Lean default-kernel replay,
successful statement/definition comparison and final exit status zero.
[axiom-verification.json](axiom-verification.json) retains every printed
internal/public declaration.

**LeanCert performs explicit kernel trust auditing of a pure exact proof;
there is no numerical interval certificate.** The actual Proof and Solution
sources select kernel mode and run eight internal plus eight public assertions.
The source contains no interval-decide or native-decide proof shortcut. Actual
complex roots of unity, the CFC modulus, Euclidean operator norm, positive-square
decomposition, dimension-two witness sums and IsLeast of the complete admissible
set all have exact proofs. Both independent mathematical referee reports and
their material dependency inspections are bound to this actual input set. This
operational audit confirms those same bytes passed the real checker; it does
not replace their independent source-to-target review.

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

- Build and export run under the recorded non-root UIDs with six private namespaces,
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

This completes the execution gate for the complete original affirmative
odd-summand sharp-constant result, proved through the stronger all-k>=2 result
in every positive dimension for every tuple of complex contractions. The
modulus and Euclidean operator norm are genuine library notions; the sharp
constant is the actual infimum of the entire nonnegative admissible set.
Attainment and IsLeast are established first. No externally assumed upper
bound or numerical phase data is used. The source's additional dimension-three
Hermitian extremizers and rank classification remain outside the eight exports.

Matthew J. Colbrook retains the mathematical result and proof, and Bourin and
Lee retain conjecture and prior-bound credit. George Stepaniants receives
AI-assisted formalization credit with the Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA
affiliation, without an email address. No priority or author-endorsement claim
is introduced by this execution audit.

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
