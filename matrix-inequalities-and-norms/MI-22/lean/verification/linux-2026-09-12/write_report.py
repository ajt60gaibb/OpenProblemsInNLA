"""Write the operational verdict only after completed-run and detailed checks pass."""
from pathlib import Path
import json,hashlib,re
out=Path(__file__).resolve().parent
read=lambda n:json.loads((out/n).read_text())
idn=read('identity-verification.json');ctrl=read('control-verification.json');tool=read('tool-source-verification.json');run=read('run-metadata.json');jobs=read('jobs.json')['jobs'];logzip=read('run-log-archive.json');idrun=read('permanent-id-run.json');idjobs=read('permanent-id-jobs.json')['jobs']
assert idn['result'].startswith('PASS') and ctrl['result']=='PASS' and tool['result']=='PASS'
assert run['conclusion']=='success' and run['status']=='completed' and idn['overall_run_success_observed']
assert all(j['conclusion']=='success' and all(s['conclusion']=='success' for s in j['steps']) for j in jobs)
commit=idn['commit'];run_id=idn['run'];project=idn['project'];count=len(idn['input_files']);assert count==177
v=next((out/'artifacts/lean-MI-22').glob('verify-*'));receipt=json.loads((v/'result.json').read_text());assert receipt['input_sha256']=={p:r['sha256'] for p,r in read('preflight.json')['input_files'].items()}
pack=json.loads((out/'source'/project/'verification/root-linux-packaging.json').read_text());freeze=json.loads((out/'source'/project/'verification/proof-freeze.json').read_text())
job=lambda name:next(j for j in jobs if j['name']==name)
pjob=next(j for j in jobs if j['name'].startswith('verify (MI-22,'))
rows='\n'.join(f"| `{a['name']}.zip` | `{a['id']}` | `{a['sha256']}` | {a['file_count']} |" for a in idn['archives'])
exports='\n'.join(f"{i+1}. `{name}`" for i,name in enumerate(ctrl['theorem_names']))
reviews='\n'.join(f"- `{name}`: `{h}`." for name,h in pack['independent_review_hashes'].items())
binaries='\n'.join(f"- `{name}`: `{h}`." for name,h in tool['linux_tool_receipt']['executables'].items())
relv=str(v.relative_to(out));idraw=(out/f"permanent-id-job-{idjobs[0]['id']}.log").read_text()
assert 'Validated 217 permanent problem IDs' in idraw and 'Ran 17 tests' in idraw and 'OK' in idraw
report=f'''# MI-22 independent Linux operational audit - 12 September 2026

**PASS.** The actual Linux run completed successfully. Both original artifact
ZIPs match GitHub's published digests and raw upload logs. All **{count}**
recorded inputs match the complete committed project tree and independently
reviewed mathematical sources. All **{len(ctrl['theorem_names'])}** exports passed the actual Comparator,
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
- Immutable candidate: [{commit}](https://github.com/sgstepaniants/OpenProblemsInNLA/commit/{commit}).
- [Lean run {run_id}](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/{run_id})
  completed **SUCCESS**. All {len(jobs)} jobs and every recorded step succeeded.
  Other problem artifacts in the same run are not independently audited here.
- Relevant jobs: selection `{job('select')['id']}`, standalone checker
  `{job('checker-controls')['id']}`, and [MI-22 `{pjob['id']}`](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/{run_id}/job/{pjob['id']}).
- Companion [permanent-ID run {idrun['id']}](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/{idrun['id']}),
  job `{idjobs[0]['id']}`, succeeded at the same commit. Its original raw log
  confirms all 217 permanent IDs and all 17 ID tests.

| Original archive | GitHub artifact ID | SHA256 matched to GitHub metadata and upload log | Extracted files |
| --- | --- | --- | --- |
{rows}

The complete original `run-logs.zip` has SHA256
`{logzip['archive_sha256']}` and contains **{logzip['file_count']}** internal log files,
whose sizes and hashes are retained in [run-log-archive.json](run-log-archive.json).
It was retrieved from GitHub's authenticated run-log endpoint. Unlike the two
artifacts above, no GitHub-published digest is claimed for that log ZIP. The
full original archives, selected raw job logs, metadata and exact extracted
bytes are preserved. Archive paths, symlink exclusion and CRC integrity were
checked.

## Reviewed source and statement identity

The actual [receipt]({relv}/result.json) records
`comparator-accepted`, the exact commit and all {count} input hashes. Its key set
matches the complete `git ls-tree` project inventory, and every byte matches
both the immutable Git blob and the candidate worktree. The complete source
snapshot is retained under `source/{project}/`; no nested evidence manifest
is omitted.

Proof-freeze SHA256 is
`f1c267a6aa600074d3b054863926d5f9cdbf6b0eadb83912a912277ac54018a0`.
All **{len(freeze['files'])-1} non-README files of its {len(freeze['files'])} inputs** remain unchanged, and the
historical README is preserved in its candidate archive. The exact source and
configuration identities from both independent final-referee evidence sets
match all eleven central mathematical/statement/source-mapping inputs. Both
final reports bind the complete proof freeze and the actual Proof/Solution
hashes. All four report hashes also match the receipt and packaging record:

{reviews}

The current candidate README and v0.4 manifest match their independently
reviewed packaging hashes and passed the actual Linux schema/coverage check.
Their pending-Linux wording accurately records the pre-execution candidate;
this audit preserves those historical bytes. All **{len(freeze['source_files'])} original canonical and
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
All **{ctrl['fresh_dependency_clones']}** dependencies were freshly cloned at their exact manifest
revisions, including LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and
Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

The official Mathlib cache decompressed **{ctrl['official_mathlib_cache_files']} files**. This was **not a
complete Mathlib source rebuild**. Actual project modules were freshly
elaborated. The graph sizes were **{ctrl['fresh_challenge_graph_jobs']} jobs** for Challenge and
**{ctrl['fresh_solution_graph_jobs']} jobs** for Solution; these numbers are not counts of newly compiled
dependency sources. Challenge's eight deliberate placeholders remain in its
isolated reference environment. Solution has no warnings or admissions. All
**{ctrl['axiom_print_count']}** internal/public transitive axiom reports contain exactly `propext`,
`Classical.choice` and `Quot.sound`; the corresponding nine internal and eight
public explicit kernel assertions ran during those builds.

The actual config and both exported environments contain precisely:

{exports}

There are **no definition exceptions**. The [main Comparator log]({relv}/comparator.log)
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
also match the candidate's reviewed upstream base. All **{tool['locked_source_count']}** immutable Forsythe
source files were independently rehashed, size-checked and retained with their
licenses. The exact reviewed CI probe was reconstructed from the pinned
original and matched to the actual Linux receipt.

- Forsythe source: `{tool['linux_tool_receipt']['forsythe_commit']}`.
- Source lock SHA256: `{tool['source_lock_sha256']}`.
- Harness SHA256: `{tool['harness_sha256']}`.
- Derived CI probe SHA256: `{tool['ci_sandbox_probe_sha256']}`.
- Actual Lean: `{tool['linux_tool_receipt']['lean_version']}`.
- Actual Go: `{tool['linux_tool_receipt']['go_version']}`.
- Linux platform: `{tool['linux_tool_receipt']['platform']}`.

Both jobs built actual Comparator/exporter and Landrun executables; their
receipts match, including these binary hashes:

{binaries}

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

The [outer evidence manifest](EVIDENCE-MANIFEST.json) binds **@BOUND_COUNT@ files**;
the retained directory contains **@TOTAL_COUNT@ files including that manifest**.
Only that exact outer path excludes itself; all nested manifests are included.
Counts are derived from actual contents. [verify_evidence.py](verify_evidence.py)
checks exact offline inventory, sizes and hashes. The complete original run-log
ZIP and its internal inventory, both artifact ZIPs, all extracted bytes and all
submitted sources are retained.

No proof, config, pin, original source, canonical page, registry or review byte
was changed. No commit, push, PR, status promotion or repeat Linux run was made.
Current publication metadata and the independent publication review remain
separate subsequent actions.
'''
(out/'OPERATIONAL-REVIEW.md').write_text(report)
print('PASS operational report prepared from observed final artifacts and independently inspected raw logs; evidence seal follows.')
