"""Write the IE-23 operational verdict from final successful evidence only."""
from pathlib import Path
import json

OUT = Path(__file__).resolve().parent
read = lambda n: json.loads((OUT / n).read_text())
c = read('context.json')
i = read('identity-verification.json')
v = read('control-verification.json')
t = read('tool-source-verification.json')
r = read('run-metadata.json')
j = read('jobs.json')['jobs']
z = read('run-log-archive.json')
ids = read('permanent-id-run.json')
idjobs = read('permanent-id-jobs.json')['jobs']
assert i['result'].startswith('PASS') and v['result'] == t['result'] == 'PASS'
assert r['status'] == 'completed' and r['conclusion'] == 'success'
assert r['head_sha'] == c['commit'] and i['overall_run_success_observed']
assert all(x['status'] == 'completed' and x['conclusion'] == 'success' for x in j)
assert all(s['status'] == 'completed' and s['conclusion'] == 'success' for x in j for s in x['steps'])
assert len(i['input_files']) == c['expected_input_count'] == 190
assert len(v['theorem_names']) == 8 and v['axiom_print_count'] == 16
assert ids['head_sha'] == c['commit'] and ids['conclusion'] == 'success'
assert len(idjobs) == 1
idlog = (OUT / f"permanent-id-job-{idjobs[0]['id']}.log").read_text()
assert 'Validated 217 permanent problem IDs' in idlog and 'Ran 17 tests' in idlog
assert 'OK' in idlog
proofjob = next(x for x in j if x['name'].startswith('verify (IE-23,'))
controljob = next(x for x in j if x['name'] == 'checker-controls')
selectjob = next(x for x in j if x['name'] == 'select')
artifact_rows = '\n'.join(f"| `{a['name']}.zip` | {a['id']} | `{a['sha256']}` | {a['file_count']} |" for a in i['archives'])
review_rows = '\n'.join(f"- `{n}`: `{h}`." for n, h in i['independent_mathematical_review_hashes'].items())
exports = '\n'.join(f"{k + 1}. `{n}`" for k, n in enumerate(v['theorem_names']))
binary_rows = '\n'.join(f"- `{n}`: `{h}`." for n, h in t['linux_tool_receipt']['executables'].items())
receipt_path = next((OUT / 'artifacts/lean-IE-23').glob('verify-*/result.json'))
receipt_rel = str(receipt_path.relative_to(OUT))
report = f'''# IE-23 actual Ubuntu operational audit — 12 September 2026

**PASS, subject to the coordinator's separate independent acceptance of this
operational evidence.** The actual run completed successfully. All **190**
submitted input files match the complete immutable Git tree and reviewed
proof/statement boundaries. All **eight** exports passed the genuine Comparator,
standard-three axiom restriction and Lean default-kernel replay. Both the
standalone checker and project job exercised their real isolation and
rejection controls. No required job or recorded step was skipped.

Inspector: `/root/leancert_examples`. **I authored the IE-23 proof.** This is
an operational execution and identity inspection, not an additional independent
mathematical proof review. The independent final mathematical referees are
`/root/solved_statement_inventory` and `/root`; their original hash-bound
reports and evidence are unchanged. The coordinator `/root` separately
reviews and accepts this operational evidence before publication. No human
peer review, official Tau Ceti endorsement or source-author endorsement is
claimed.

## Actual run and original evidence

- Candidate: [{c['commit']}](https://github.com/{c['repository']}/commit/{c['commit']}).
- [Lean verification run {c['run']}](https://github.com/{c['repository']}/actions/runs/{c['run']})
  completed **SUCCESS**, with all **{len(j)} jobs** and every recorded step
  successful. Selection job `{selectjob['id']}`, standalone checker
  `{controljob['id']}`, and [IE-23 job {proofjob['id']}](https://github.com/{c['repository']}/actions/runs/{c['run']}/job/{proofjob['id']})
  were inspected directly. Other project artifacts in this run are outside
  this audit.
- [Permanent-ID run {ids['id']}](https://github.com/{c['repository']}/actions/runs/{ids['id']})
  also passed at the exact same commit. Its original log confirms all 217
  permanent IDs and all 17 ID tests. The candidate commit records George
  Stepaniants with empty author and committer emails.

| Original archive | Artifact ID | SHA256 matched to GitHub metadata and raw upload log | Files |
| --- | --- | --- | --- |
{artifact_rows}

The original complete `run-logs.zip` has SHA256 `{z['archive_sha256']}`
and contains **{z['file_count']}** internal log files, individually inventoried
in [run-log-archive.json](run-log-archive.json). It came from the authenticated
GitHub run-log endpoint; no GitHub-published digest is claimed for that log
ZIP. Both artifact ZIPs, raw metadata pages, selected unmodified job logs,
exact extracted artifact bytes and the full original run-log ZIP are retained.
Artifact upload IDs and digests match their actual raw upload steps.
ZIP path safety, symlink exclusion, duplicate names and CRC checks passed.
Paginated metadata is retained with its original pages and complete key sets.

Initial selected-job retrieval occurred while unrelated jobs were still
running. Its separately named metadata records that fact. Final retrieval
and the actual final audit required observed whole-run success; the initial
record was not treated as a final execution verdict.

## Complete identity and prior independent review boundary

The actual [project receipt]({receipt_rel}) says `comparator-accepted`, records
the exact commit and enumerates the complete **190-file** project. Its key
set equals `git ls-tree`; every recorded hash matches both the immutable
Git blob and the candidate worktree. The exact Git project and all original
sources are retained under `source/`, including every nested manifest.

The original proof freeze is `{c['proof_freeze_sha256']}`. All **103 non-README
inputs among its 104 files** remain byte-identical. Its historical README is
retained exactly in `verification/linux-candidate-2026-09-12/README.statement.md`.
The original 32-file statement boundary, eight original source files, additive
Comparator supplement, eight proof module/wrapper identities, all four
independent report hashes and every bound reviewer evidence file match:

{review_rows}

Both final mathematical audits bind the same full proof freeze, 93 reachable
project declarations, ten fresh local commands and all eight exact theorem
headers. Their actual implementation-source hashes match the submitted
modules. The packaging changes only historical README wording, adding current
metadata and documentation evidence. The root packaging manifest
`{c['root_packaging_manifest_sha256']}` binds all 22 files including the nested
18-item preparer manifest; all match the actual input set. The current
README and v0.4 manifest match their separately approved hashes and passed
the actual Linux schema/coverage check. Their Linux-pending wording is an
accurate historical description of the pre-execution candidate and remains
unchanged in this evidence.

The original canonical and Colbrook source bytes match the reviewed base
`{c['source_base']}`. The permanent target and canonical **Solved** status
have not been changed by this audit. [identity-verification.json](identity-verification.json)
and [preflight.json](preflight.json) retain all checked identities.

## Fresh elaboration and actual kernel/Comparator verification

The immutable harness snapshots ordinary committed sources into a fresh
`{v['fresh_project_directory']}` directory. It excludes tracked compiled
artifacts, rejects symlinks and verifies source hashes after dependency
materialization, cache retrieval and Comparator execution. Controls run
before any candidate Solution build. All **{v['fresh_dependency_clones']}** dependencies are freshly
cloned at their exact manifest revisions. Mathlib is
`0df444a360eaa60ab8c11dca51a86af692955474`; LeanCert is
`621a43d7cf21f87872392a01e874f2f1dbddc926`.

The official Mathlib cache decompressed **{v['official_mathlib_cache_files']} files**. This is not a
full Mathlib source rebuild. The actual fresh Challenge and Solution graph
sizes are **{v['fresh_challenge_graph_jobs']}** and **{v['fresh_solution_graph_jobs']}** jobs, respectively; those are graph
sizes, not counts of newly compiled dependency files. Seven actual project
modules and Solution were freshly elaborated. Challenge's eight intentional
placeholders remain isolated in the reference environment. Solution has no
warnings or admissions. All **16** internal/public transitive axiom reports
contain exactly `propext`, `Classical.choice` and `Quot.sound`; eight internal
and eight public explicit LeanCert kernel assertions run during these builds.

Actual configuration and both exports select exactly:

{exports}

There are **no definition exceptions**. Both builds, both exports, successful
default-kernel replay, statement/definition comparison and final exit zero
are present in the actual Comparator log. The main command uses the real
strict Landrun wrapper in a systemd service with `RestrictAddressFamilies=~AF_UNIX`
and the constrained environment. No skip-kernel flag is present.

**LeanCert supplies explicit kernel trust auditing of a pure exact proof;
there is no numerical interval certificate.** This role was approved before
proof implementation. The actual norms, real powers, matrix rank/inverse,
nonzero-input suprema and all-complex global-minimizer bridges are exact
proofs bound to the independent mathematical reviews. This audit confirms
those exact bytes passed the real checker and does not substitute for those
source-to-target reviews.

## Checker source identity and exercised rejection phases

All 58 immutable Forsythe tool files were independently rehashed, size-checked
and retained with their licenses. Harness, source lock, bootstrap, selftest
and verify files are unchanged from audited infrastructure
`214c142d6bfe0f0c338808f188062acbbad0fb19`; the workflow and toolchain agree
with the candidate's source base. The exact CI probe derivation was
reconstructed from the pinned original and matches both Linux receipts.

- Forsythe commit: `{t['linux_tool_receipt']['forsythe_commit']}`.
- Source lock: `{t['source_lock_sha256']}`.
- Harness: `{t['harness_sha256']}`.
- Derived CI probe: `{t['ci_sandbox_probe_sha256']}`.
- Actual Lean: `{t['linux_tool_receipt']['lean_version']}`.
- Actual Go: `{t['linux_tool_receipt']['go_version']}`.
- Actual platform: `{t['linux_tool_receipt']['platform']}`.

Both jobs freshly build the checker/exporter and Landrun binaries. Their
receipts agree, including these actual executable hashes:

{binary_rows}

I read the full actual project and standalone control logs. In **each** suite:

- Build and export run as non-root UID 1001 with six private namespaces,
  no effective capabilities and `no_new_privs`. Host-process lookup/signaling,
  loopback networking and AF_UNIX creation fail. Outside writing, truncation,
  creation and symlink escape fail. The designated build fixture write succeeds;
  export writes/truncations fail and the remaining fixture contents are unchanged.
- Nested Bubblewrap actually runs but UID-map creation is denied **before
  any inner write executes**. Four unsupported or widening sandbox options
  reject with exit two. No broader all-attacks guarantee is inferred.
- The honest raw-kernel inductive/quotient fixture succeeds. The malformed
  raw proof fails the kernel's declaration-type check. The changed `Quot.lift`
  passes kernel replay and then fails the quotient post-check.
- All five Comparator fixtures build/export both environments and reach
  their required actual phases. The honest fixture passes; other fixtures
  reject constant kind, `helper` axiom or theorem statement as actually logged.
  In particular, the `simple_kind_mismatch` fixture's observed rejection is
  the forbidden `helper` axiom, not a separately inferred kind error.
- The extra real admitted-proof and native-proof fixtures also build/export
  both environments, then fail for `sorryAx` and
  `checked._native.native_decide.ax_1_1`. Their expected exit-one statuses
  are checked by the successful enclosing harness.

[RAW-LOG-READING.md](RAW-LOG-READING.md), [control-verification.json](control-verification.json),
[axiom-verification.json](axiom-verification.json), and the original runtime
logs retain the detailed observations. [audit_checks.py](audit_checks.py)
rechecks every identity and required phase; the sources and exact original
log bytes remain available for the coordinator's independent acceptance.

## Scope, credit and inventory

The complete canonical universal direct induced p-to-2 norm uniqueness
conjecture is negated, preserving all original dimensions, full-row-rank
complex matrices and finite real p>2. The unchanged rational example at
p=4 supplies two distinct **global** minimizers over every complex right
inverse, both with the actual induced norm equal to the positive fourth root
of two. Generic denominator/supremum semantics are proved on the original
domain. The source's stronger all-p formulas, complete classifications and
higher-dimensional families remain outside these eight exports.

Matthew J. Colbrook retains mathematical authorship. Dokmanić and Gribonval
retain credit for the underlying example and original question. George
Stepaniants receives AI-assisted formalization credit with the Department of
Computing and Mathematical Sciences, California Institute of Technology,
Pasadena, California, USA affiliation and no email address. Shared tools
retain attribution and licenses. No priority or source-author endorsement
is introduced.

The outer [evidence manifest](EVIDENCE-MANIFEST.json) binds **@BOUND_COUNT@ files**,
with **@TOTAL_COUNT@ files including itself**. It excludes only its exact own
path, retaining all nested manifests. [verify_evidence.py](verify_evidence.py)
checks the exact offline inventory, sizes and hashes. Original ZIPs and
receipts, all selected raw logs, full run-log inventory, all candidate sources,
eight originals and all pinned checker sources are retained.

No candidate proof, pin, configuration, review, canonical source, registry or
metadata byte was changed. No local dependency build, new run, commit, push,
PR or status promotion was performed. Independent coordinator acceptance and
publication review are separate remaining gates.
'''
(OUT / 'OPERATIONAL-REVIEW.md').write_text(report)
print('Operational report generated from final successful actual run, exact sources and manually inspected raw phases; evidence sealing follows.')
