from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, yaml

R = Path('/tmp/nla-lean-ra09-worktree')
E = R/'randomized-and-low-rank-approximation/RA-09'
P = E/'lean'
O = P/'verification/publication-2026-09-13'
C = '3bcc863070c037fffb1deee3f12d1cd1517727df'
BASE = '5830ed4fb06da0659414a3deb2a40ad327aca052'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
git = lambda *a: subprocess.check_output(['git', *a], cwd=R)
assert git('rev-parse', 'HEAD').decode().strip() == C
assert not git('diff', '--name-only', 'HEAD') and not O.exists()
marker = Path('/tmp/nla-lean-formalization/ra09-pdf-operation-marker.log')
assert marker.exists()
assert sha(P/'verification/root-operational-2026-09-13/ROOT-CHECKS.json') == '11842634cf4de0fd7da47af0bc4c3aeff6c3cbaad410e1a2c53cd2eaf2b263ee'
inputs = {}
project_rel = P.relative_to(R).as_posix()
for path in git('ls-tree', '-r', '--name-only', C, '--', project_rel).decode().splitlines():
    rel = str(Path(path).relative_to(project_rel))
    digest = hashlib.sha256(git('show', C+':'+path)).hexdigest()
    assert sha(P/rel) == digest
    inputs[rel] = digest
assert len(inputs) == 524
prior = {}
for f in P.rglob('*'):
    assert not f.is_symlink(), f
    if f.is_file(): prior[str(f.relative_to(P))] = sha(f)
assert len(prior) == 1235
immutable = {}
for name, count, expected in [
    ('linux-2026-09-13', 703, '56dd2e10ca4d4f16367f85d06fde4630f66df2e4ac12dfbace9637e97b49de90'),
    ('root-operational-2026-09-13', 6, 'e80edf4c6d85bcfc58ab3534cd213c4e52b5416721361206682bf0f8223f66b9')]:
    root = P/'verification'/name
    outer = root/'EVIDENCE-MANIFEST.json'
    assert sha(outer) == expected
    records = json.loads(outer.read_text())['files']
    actual = {str(f.relative_to(root)) for f in root.rglob('*') if f.is_file() and f != outer}
    assert actual == set(records) and len(records) == count
    for rel, v in records.items():
        assert sha(root/rel) == v['sha256'] and (root/rel).stat().st_size == v['bytes']
    immutable.update({str(f.relative_to(P)): sha(f) for f in root.rglob('*') if f.is_file()})
assert len(immutable) == 711
canonical = (E/'README.md').read_text()
target_marker = 'Let $`n\\ge2`$'
assert canonical.count(target_marker) == 1
target = canonical[canonical.index(target_marker):]
config = json.loads((P/'comparator.json').read_text())
names = config['theorem_names']
assert len(names) == 17 and names[-1] == 'NLA.RA09.concaveFrobeniusTransferConjecture'
O.mkdir()
(O/'archive').mkdir()
for n, dst in [('README.md', 'README.linux-candidate.md'), ('formalization.yaml', 'formalization.linux-candidate.yaml')]:
    (O/'archive'/dst).write_bytes((P/n).read_bytes())
(O/'artifact-operation-marker.log').write_bytes(marker.read_bytes())
(O/'before.json').write_text(json.dumps({
    'utc': datetime.now(timezone.utc).isoformat(), 'candidate': C, 'base': BASE,
    'candidate_inputs': inputs, 'all_prior_project_files': prior,
    'immutable_operational_files': immutable,
    'canonical_target_sha256': hashlib.sha256(target.encode()).hexdigest(),
    'registry_sha256': sha(R/'problem_ids.json'),
    'expected_changed_candidate_inputs': ['README.md', 'formalization.yaml'],
    'role': 'Root publication preparer and disclosed proof coauthor; no additional independent mathematical review',
    'marker_command': 'node /Users/georgestepaniants/.codex/plugins/cache/openai-primary-runtime/pdf/26.904.11930/skills/pdf/container_tools/mark_artifact_operation_started.mjs --operation-kind edit --expected-output-count 1 --output-format pdf',
    'marker_exit_code': 0,
    'marker_timing': 'Executed successfully once immediately before this first publication authoring command; raw output retained.'
}, indent=2)+'\n')

canonical = canonical.replace('**Last checked:** 2026-09-11  \n**Status:** Solved  \n', '**Last checked:** 2026-09-13\n\n**Status:** Lean verified\n', 1)
old = 'Verification is independent agent review, not external human peer review or formal certification.'
assert old in canonical
canonical = canonical.replace(old, 'That dated manuscript audit was independent agent review. The separate Lean verification below certifies the full original target; external human peer review is not claimed.', 1)
section = '''## Lean proof and verification evidence — 2026-09-13

**Formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. **Matthew J. Colbrook retains mathematical authorship.**

The [proof at immutable revision 3bcc8630](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/3bcc863070c037fffb1deee3f12d1cd1517727df/randomized-and-low-rank-approximation/RA-09/lean/Solution.lean) proves the complete original implication for every dimension, rank, ordered real PSD pair, allowed function, error parameter and selected ordered eigenbasis. It retains the difference-of-squared-norms premise and permits $`f(0)>0`$. Proved semantic bridges connect the definitions to the actual Frobenius norm, PSD order, spectral theorem and continuous functional calculus; ordinary and function truncations use the same selected eigenvectors. The trace-deficit reduction, selected zero eigenvalues and zero-tail cases are proved.

The full target is `NLA.RA09.concaveFrobeniusTransferConjecture`. All 17 checked exports in namespace `NLA.RA09` are:

'''
for i in range(0, len(names), 2):
    section += '- ' + '; '.join('`'+n.removeprefix('NLA.RA09.')+'`' for n in names[i:i+2]) + '.\n'
section += '''
The [proof map](lean/PROOF_MAP.md) and [manifest](lean/formalization.yaml) give each contract and its original-target correspondence. Exact unbounded scalar factorizations and a sum of squares eliminate interval computations. LeanCert checks kernel trust throughout the matrix proof. The manuscript's broader function class, unordered theorem and ancillary extensions are outside these exports.

Two independent statement approvals preceded implementation; [two independent final mathematical reviews](lean/README.md#reviewed-evidence) approved the frozen proof. [Ubuntu run 34738884548](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34738884548), on 13 September 2026, matched all 17 exports without definition exceptions and replayed them through Lean's default kernel. All 49 source axiom reports permit only `propext`, `Classical.choice`, and `Quot.sound`; both actual control suites passed as a non-root user. The [independent operational audit](lean/verification/linux-2026-09-13/OPERATIONAL-REVIEW.md) and [coordinator acceptance](lean/verification/root-operational-2026-09-13/ROOT-CHECKS.json) bind the complete 524-file candidate. Local macOS development checks are recorded separately.

The checked toolchain is **Lean 4.33.1**. Dependency revisions are:

- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
- LeanCert: `621a43d7cf21f87872392a01e874f2f1dbddc926`.

The [Lake manifest](lean/lake-manifest.json) pins all ten dependencies. The run used a fresh project and matching official Mathlib cache objects; it did not rebuild all dependencies from source. From a clean checkout of immutable revision `3bcc863070c037fffb1deee3f12d1cd1517727df`, use a non-root Linux host with the [documented prerequisites](../../tools/lean/HARNESS.md) and run from the repository root:

```
tools/lean/bootstrap.sh /tmp/nla-ra09-check
tools/lean/selftest.sh /tmp/nla-ra09-check
tools/lean/verify.sh randomized-and-low-rank-approximation/RA-09/lean \\
  /tmp/nla-ra09-check
```

These commands run the controls, statement comparison, permitted-axiom checks and default-kernel replay. A local `lake build Solution` is a separate development check. The original statement and source record below remain unchanged.

## Problem statement

'''
canonical = canonical.replace(target_marker, section+target_marker, 1)
assert canonical[canonical.index(target_marker):] == target
(E/'README.md').write_text(canonical)

readme = (P/'README.md').read_text()
old = readme.splitlines()[2]
assert 'Linux verification is pending' in old
readme = readme.replace(old, '**The complete seventeen-export proof passed two independent mathematical reviews and actual Ubuntu Comparator/default-kernel verification.** The [canonical problem](../README.md) records its full original target as **Lean verified**. The checked immutable revision and retained evidence are documented below.', 1)
old = 'The latter now prepares these candidate documents; that role adds no mathematical approval.'
assert old in readme
readme = readme.replace(old, 'The latter subsequently prepared candidate documents and conducted the operational audit; those roles add no mathematical approval.', 1)
old = 'Actual non-root Ubuntu Comparator/default-kernel replay and rejection controls, operational review and publication remain pending.'
assert old in readme
readme = readme.replace(old, 'Actual non-root Ubuntu Comparator/default-kernel replay and rejection controls have passed, followed by independent operational review and coordinator acceptance. Publication review is the remaining gate.', 1)
old = "The unchanged default target is Challenge. The authoritative check must run on the immutable candidate using the repository's [Linux workflow](../../../.github/workflows/lean-verification.yml) and [pinned verification instructions](../../../docs/lean/README.md). Local builds and these reviews do not stand in for that check."
assert old in readme
readme = readme.replace(old, "The unchanged default target is Challenge. Reproduce the authoritative check on immutable candidate `3bcc863070c037fffb1deee3f12d1cd1517727df` using the repository's [Linux workflow](../../../.github/workflows/lean-verification.yml), [pinned verification instructions](../../../docs/lean/README.md), and the exact commands on the [canonical page](../README.md#lean-proof-and-verification-evidence---2026-09-13). Local builds are separate development checks.", 1)
readme += '''

## Actual Ubuntu verification and publication preservation

[Run 34738884548](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34738884548) verified immutable candidate `3bcc863070c037fffb1deee3f12d1cd1517727df`. All 17 jobs and every step passed. The actual RA-09 job ran on Ubuntu 24.04 x86_64 with Lean 4.33.1, the pinned Comparator/exporter and the strict sandbox as UID 1001. It freshly checked out all ten dependency revisions and used 8,690 matching official Mathlib cache objects. Challenge/Solution graph sizes were 2,710/2,726 jobs; this is not a claim to rebuild all dependencies from source.

Both actual export lists contain exactly the seventeen advertised declarations without definition exceptions. Default-kernel replay accepted Solution. All 49 embedded LeanCert kernel assertions and standard-three reports passed; the Solution build emitted no warnings or admissions. The final referees' 66 and 50 reports include their additional independent diagnostic checks and remain separately recorded.

The target and standalone checker jobs each ran the actual sandbox probes, three raw-kernel controls, five Comparator fixtures and actual admission/native rejection controls. Bad exported proofs were rejected for `sorryAx` and `checked._native.native_decide.ax_1_1`. The nested Bubblewrap executable was denied UID-map setup before its inner write ran; this is not an observed inner-write denial or a general sandbox-security proof.

The [independent operational report](verification/linux-2026-09-13/OPERATIONAL-REVIEW.md) and [complete manifest](verification/linux-2026-09-13/EVIDENCE-MANIFEST.json) bind 703 files plus the outer manifest, including all thirteen nested candidate manifests and all 524 committed project inputs. The original project ZIP has SHA256 `f4be34322f3b97935c20bcca0a9b3538ff010e69df0e822569716fb41df8135f`; the control ZIP has SHA256 `b948e6a6a81e9b138965f4bf1e98a9fe382d56bb51e889c4c50e9b9c541740da`. Both agree with GitHub metadata and actual upload logs. The complete 217-file run-log ZIP is retained with locally computed SHA256 `b204c7a65910570275a9354aa45db865219113b64e7701fa35e0a0b7b1fc99b3`; no GitHub-published digest for that log ZIP is claimed. All permanent-ID checks and 17 tests passed.

Operational reviewer /root/mf16_final_referee previously served as independent final mathematical referee 2 and candidate-document preparer. /root/formal_review_standards independently reviewed the concrete candidate packaging. Root, a disclosed proof coauthor, accepted the operational evidence and prepared these publication wrappers. These subsequent roles do not increase the two independent final mathematical referee approvals. The [root acceptance](verification/root-operational-2026-09-13/ROOT-CHECKS.json) and its complete manifest bind six files plus the outer manifest.

The actual Linux run verified the immutable candidate. Publication changes only README.md and formalization.yaml among its 524 inputs, archiving both exact originals under [publication evidence](verification/publication-2026-09-13/archive/). All 522 other candidate inputs, 704 Linux evidence files and seven root operational files remain unchanged. All 361 proof inputs, 31 statement inputs and 17 original source/policy inputs remain preserved through exact historical wrapper archives. The original mathematical suffix, source manuscripts and all nested manifests remain intact. Earlier pending notices are historical records.

Independent publication review precedes the publication commit, normal fork push and new upstream main PR. No new proof execution, external human review, official Tau Ceti endorsement or new mathematical priority is claimed by this documentation update.
'''
(P/'README.md').write_text(readme)

path = P/'formalization.yaml'
header = path.read_text().splitlines()[0]
d = yaml.safe_load(path.read_text())
d['status']['scope'] = 'Complete seventeen-export affirmative proof of the full original real ordered-PSD concave Frobenius-transfer implication, with its difference-of-squared-norms premise, all selected eigenbases and f(0)>0 retained. Two independent statement approvals preceded implementation; two independent final mathematical reports were accepted. Actual Ubuntu run 34738884548 at '+C+' passed all 17 jobs, all exports, default-kernel replay, 49 embedded kernel/standard-three reports and both actual control suites. Independent operational audit and root acceptance bind all 524 inputs. Canonical status is Lean verified; publication review remains a separate gate.'
d['review']['status'] = 'agent-reviewed; Linux-Comparator-and-default-kernel-verified'
old = 'Actual Ubuntu, standalone default-kernel replay, Comparator, sandbox/rejection controls and operational acceptance are separate pending gates.'
assert old in d['review']['notes']
d['review']['notes'] = d['review']['notes'].replace(old, 'Actual Ubuntu run 34738884548 passed all 17 jobs and steps, all seventeen matched exports, default-kernel replay and 49 embedded kernel/standard-three reports. Both actual control suites passed as UID 1001. Ten fresh dependency checkouts used 8,690 matching official Mathlib cache files; no full dependency-source rebuild is claimed. Nested Bubblewrap was denied UID-map setup before its inner write. Independent operational referee /root/mf16_final_referee is also final referee 2 and prior candidate-document preparer; its complete 703-file evidence inventory plus outer and all thirteen nested candidate manifests preserve all 524 candidate inputs. Root accepted this in its disclosed proof-coauthor role. The root acceptance SHA256 is 11842634cf4de0fd7da47af0bc4c3aeff6c3cbaad410e1a2c53cd2eaf2b263ee. Exact candidate wrappers are archived before this update. Separate publication review remains required; no extra mathematical approval is claimed.')
d['review']['linux_verification']['status'] = 'passed; independently audited and root accepted'
d['review']['linux_verification']['note'] = 'Actual run https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34738884548 at '+C+'. All 17 exports, default-kernel replay, 49 standard-three source reports and both real control suites passed. Original artifact ZIPs, all 217 run logs and the complete 524-input snapshot are retained in verification/linux-2026-09-13. Operational report SHA256 56aec1e09de54a0b0aea0545fc6fd0fc54f2c5d5e4b52c1e8b3870ade5d66a0d; complete outer manifest SHA256 56dd2e10ca4d4f16367f85d06fde4630f66df2e4ac12dfbace9637e97b49de90. See verification/root-operational-2026-09-13/ROOT-CHECKS.json for coordinator acceptance. Actual Linux checked the immutable candidate; its wrappers are archived before this publication update.'
d['review']['candidate_documents']['installation'] = 'Root installed candidate wrappers after the accepted final-review gate; the exact historical README and external draft remain retained. Independent concrete packaging review and actual Linux verification subsequently passed. The exact candidate README and manifest are now archived under verification/publication-2026-09-13/archive before the current publication-only update. No Lean source or frozen mathematical target changed.'
path.write_text(header+'\n'+yaml.safe_dump(d, sort_keys=False, allow_unicode=True, width=100))

s = (R/'RESOLVED.md').read_text()
marker = '**RA-09 (Solved).**'
a = s.index(marker)
b = s.index('\n\n', a)
block = s[a:b].replace(marker, '**RA-09 (Lean verified; formalization by George Stepaniants).**', 1)
block += ''' **Lean verification — 2026-09-13:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. Matthew J. Colbrook retains mathematical authorship. The [seventeen exports](randomized-and-low-rank-approximation/RA-09/lean/Solution.lean) prove the full original concave Frobenius-transfer implication, including its trace-deficit premise, every allowed ordered eigenbasis and functions with positive value at zero. Genuine Frobenius norm, PSD order and CFC are linked by proved semantic bridges. Exact scalar algebra and LeanCert kernel trust checks require no interval computation. Two independent statement and two independent final mathematical approvals were followed by [Ubuntu run 34738884548](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34738884548), with all seventeen exports, default-kernel replay, 49 standard-three reports and both actual control suites passing. The [canonical evidence](randomized-and-low-rank-approximation/RA-09/README.md#lean-proof-and-verification-evidence---2026-09-13) gives immutable sources, exact declarations, pins, commands and the independent operational audit binding all 524 inputs. External human peer review is not claimed.'''
(R/'RESOLVED.md').write_text(s[:a]+block+s[b:])
(O/'prepare.py').write_bytes(Path(__file__).read_bytes())
for rel, digest in prior.items():
    if rel not in ['README.md', 'formalization.yaml']: assert sha(P/rel) == digest, rel
assert sha(R/'problem_ids.json') == json.loads((O/'before.json').read_text())['registry_sha256']
print(json.dumps({'prepared': 'RA-09', 'candidate_inputs': 524, 'prior_project_files': 1235, 'immutable_operational_files': 711, 'target_unchanged': True}, indent=2))
