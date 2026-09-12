from pathlib import Path
from datetime import datetime, timezone
import collections
import hashlib
import json
import re
import subprocess
import yaml

repo = Path('/tmp/nla-lean-tr15-worktree')
entry = repo / 'tensor-computations/TR-15'
project = entry / 'lean'
linux = project / 'verification/linux-2026-09-12'
pub = project / 'verification/publication-2026-09-12'
revision = '6a2d0868e8b7905dbd5c04d4beaae8cf43288e1f'
base = 'f41f1f9ffa2171550d4bb795862c6170c4f26070'
work = Path('/tmp/nla-lean-formalization/tr15-publication')

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def git(*args):
    return subprocess.check_output(['git', *args], cwd=repo)

before_merge = json.loads((work / 'before-integration.json').read_text())
integration = json.loads((work / 'integration.json').read_text())
assert git('rev-parse', 'HEAD').decode().strip() == integration['integration_commit']
assert subprocess.run(['git', 'merge-base', '--is-ancestor', base, 'HEAD'], cwd=repo).returncode == 0
for group in ['verified_inputs', 'operational_files']:
    for name, expected in before_merge[group].items():
        assert sha(project / name) == expected, name
assert not pub.exists()
pub.mkdir()
canonical = (entry / 'README.md').read_text()
target = canonical[canonical.index('## Statement'):]
registry = json.loads((repo / 'problem_ids.json').read_text())
counts = collections.Counter(re.search(r'^\*\*Status:\*\*\s+([^\n]+)', (repo / p).read_text(), re.M).group(1).strip() for p in registry.values())
baseline = {
    'verified_revision': revision,
    'verified_run': 34716902324,
    'base': base,
    'integrated_head': integration['integration_commit'],
    'all_verified_inputs': before_merge['verified_inputs'],
    'all_operational_evidence': before_merge['operational_files'],
    'canonical_target_tail_sha256': hashlib.sha256(target.encode()).hexdigest(),
    'other_canonical': {k: sha(repo / p) for k, p in registry.items() if k != 'TR-15'},
    'problem_ids_sha256': sha(repo / 'problem_ids.json'),
    'branch_counts_before': dict(counts),
    'created_utc': datetime.now(timezone.utc).isoformat(),
}
(pub / 'before.json').write_text(json.dumps(baseline, indent=2) + '\n')
for name in ['integration.json', 'integration.log']:
    (pub / name).write_bytes((work / name).read_bytes())

section = r'''## Lean proof and verification evidence - 2026-09-12

**The complete odd-order inheritance conjecture is false, with a Lean-verified counterexample.** The [proof at revision 6a2d086](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/6a2d0868e8b7905dbd5c04d4beaae8cf43288e1f/tensor-computations/TR-15/lean) uses $`m=3`$, $`q=2`$, $`n=2`$ and the shared generator $`h=(2,0,1,0,2,0,-1)`$. Every real H-eigenvalue of the lower tensor is strictly positive, while the upper tensor has the exact H-eigenpair $`(-1,(0,1))`$.

**Mathematical counterexample and informal proof:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance.

The definitions retain every original odd $`m\ge3`$, integer $`q\ge2`$, dimension $`n\ge2`$ and real common generator. They use the actual Hankel entries, every ordered contraction tuple, signed coordinate powers and nonzero real H-eigenvectors. The seven [checked exports](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/6a2d0868e8b7905dbd5c04d4beaae8cf43288e1f/tensor-computations/TR-15/lean/Solution.lean), each with prefix `NLA.TR15.`, are:

- `lower_contractions`: all three exact component polynomials for every real vector.
- `upper_contraction`: the actual order-six contraction at $`(0,1)`$.
- `lower_eigenvalues_pos`: positivity of every lower real H-eigenvalue.
- `lower_eigenpair_exists`: a genuine nonzero lower pair from the intermediate value theorem.
- `upper_negative_eigenpair`: the complete upper pair and strict negative eigenvalue.
- `counterexample`: original admissibility, the lower premise and failure of the upper conclusion.
- `not_inheritanceConjecture`: negation of the complete universal inheritance assertion.

Lower positivity follows from the first contraction, a strictly positive sum of squares. The upper contraction has one surviving ordered tuple. An actual intermediate-value root supplies the lower pair; its existence is proved without adding a premise or a strong-Hankel hypothesis.

Two independent agents approved the [statements and completed proof](lean/reviews/). [Linux run 34716902324](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34716902324) matched all seven exports with the sandboxed Comparator and replayed the solution in Lean's default kernel. The [original artifacts and independent audit](lean/verification/linux-2026-09-12/) bind all 135 input hashes and both actual isolation/rejection-control suites. All 15 [internal/public transitive axiom reports](lean/verification/linux-2026-09-12/axiom-verification.json) use only `propext`, `Classical.choice` and `Quot.sound`. These are independent agent reviews, without a claim of external human peer review.

The proof pins **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). The kernel-mode LeanCert certificate $`-1<0`$ remains in the final negative-pair contradiction. See the [manifest](lean/formalization.yaml), [dependency pins](lean/lake-manifest.json) and [exact targets](lean/NUMERICAL_TARGETS.md). From the verified revision on a documented [non-root Linux host](../../tools/lean/HARNESS.md), reproduce with:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  tensor-computations/TR-15/lean \
  /absolute/path/to/nla-lean-tools
```

'''
canonical = canonical.replace('**Status:** Solved  ', '**Status:** Lean verified', 1)
canonical = canonical.replace('**Last checked:** 2026-09-11  ', '**Last checked:** 2026-09-12', 1)
canonical = canonical.replace('<!-- colbrook-unclaimed -->', section + '<!-- colbrook-unclaimed -->', 1)
canonical = canonical.replace(
    'No external human peer review or formal verification is asserted.',
    'The 2026-09-11 review did not assert external human peer review or formal verification. The later Lean verification above covers the complete original implication and proves the premise is nonvacuous.', 1)
assert canonical[canonical.index('## Statement'):] == target
(entry / 'README.md').write_text(canonical)

readme = (project / 'README.md').read_text()
start = readme.index('The complete seven-export proof')
end = readme.index('\nThe mathematical counterexample', start)
readme = readme[:start] + '''The complete original inheritance assertion has a **Lean-verified negative
answer** as of 12 September 2026. Its unchanged proof at
[revision 6a2d086](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/6a2d0868e8b7905dbd5c04d4beaae8cf43288e1f/tensor-computations/TR-15/lean)
passed two independent statement reviews before implementation, two independent
final proof reviews, and actual Linux sandboxed Comparator/default-kernel
verification in [run 34716902324](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34716902324).
The [independent operational audit and original artifacts](verification/linux-2026-09-12/)
bind all seven exports and the complete 135-file verified input set. The
[canonical entry](../README.md) records the full verified scope and status.
''' + readme[end:]
readme = readme.replace(
    'terms. These macOS checks reused ten verified clean pinned dependency caches;\nthey do not claim full dependency-source rebuilds or a project-specific Linux run.',
    '''terms. These local macOS checks reused ten verified clean pinned dependency
caches. The later Linux job freshly cloned all ten dependencies at their exact
revisions and used 8690 official Mathlib cache artifacts before building the
project source. It does not claim to rebuild every dependency from source.
The project and separate checker jobs both passed real isolation and rejection
controls. The nested Bubblewrap executable was denied UID-map creation before
its inner write; no general sandbox-security guarantee follows from that probe.''')
readme = readme.replace(
    'Only this current README changes among the 75 frozen project inputs; all 74\nothers and all six original canonical/manuscript sources remain byte-identical.',
    '''At candidate packaging, only the current README changed among the 75
proof-freeze inputs. Publication changes only this README and the current
formalization manifest among the 135 Linux-verified input files; all other 133,
including mathematical sources, statements, configurations, pins and prior
reviews, remain identical. All 254 retained operational evidence files are
unchanged, including the original metadata snapshots and nested manifests.
The successful run remains bound to the immutable proof revision; no new run
over these publication wrappers is claimed. The canonical target and original
informal manuscript remain unchanged.''')
readme += '''
The [complete Linux evidence manifest](verification/linux-2026-09-12/EVIDENCE-MANIFEST.json)
retains both original ZIPs, raw logs, every submitted input hash, checked tool
sources and the independent operational report. From the immutable verified
revision on a documented [non-root Linux host](../../../tools/lean/HARNESS.md), run:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \\
  tensor-computations/TR-15/lean \\
  /absolute/path/to/nla-lean-tools
```
'''
(project / 'README.md').write_text(readme)

yaml_path = project / 'formalization.yaml'
header = yaml_path.read_text().splitlines()[0]
manifest = yaml.safe_load(yaml_path.read_text())
manifest['status']['scope'] = (
    'Complete negative answer to the original canonical TR-15 implication, plus unconditional '
    'existence of a real lower H-eigenpair. All seven exports passed two independent statement '
    'reviews, two independent final proof reviews and actual Linux sandboxed Comparator/default-kernel '
    'verification in run 34716902324 on 2026-09-12 at unchanged proof revision '
    '6a2d0868e8b7905dbd5c04d4beaae8cf43288e1f. The independent operational audit binds all 135 '
    'inputs, original artifact digests and both actual isolation/rejection-control suites. '
    'Canonical status is Lean verified.')
manifest['review']['status'] = 'agent-reviewed; Linux-Comparator-and-default-kernel-verified'
manifest['review']['notes'] = (
    'Both statement approvals precede implementation and bind unchanged Definitions, Challenge, '
    'numerical targets and source correspondence. Both final referees freshly re-elaborated the '
    'actual proof in separate object prefixes and inspected the tensor, IVT and retained LeanCert '
    'certificate semantics. All 15 internal/public declarations have exactly propext, Classical.choice '
    'and Quot.sound as transitive axioms; all kernel trust checks passed. The seven deliberate '
    'Challenge placeholders remain isolated. The kernel-mode minus-one sign certificate remains '
    'in the negative pair and complete conjecture contradiction. Local macOS checks used clean '
    'exact pinned caches. Actual Linux run 34716902324 at revision '
    '6a2d0868e8b7905dbd5c04d4beaae8cf43288e1f matched all seven exports, replayed the solution '
    'in the default kernel and passed both real control sets. Independent agent '
    '/root/solved_statement_inventory audited original ZIP bytes, raw logs, all 135 inputs, ten '
    'fresh dependency clones and 8690 official Mathlib cache artifacts. No full dependency-source '
    'rebuild is claimed. The nested Bubblewrap executable was denied UID-map creation before '
    'its inner write. Operational report SHA256 '
    '904179c04b6793dee1fada9a7459982569d7f63a40dc371298915aa342871afe and outer evidence manifest '
    'df02ced673f90b753f9e49ec00dbd294b535603358c884a4b15e7db2ce0e9b8d bind 253 files plus itself, '
    'including the nested source manifest. Publication changes only this manifest and project '
    'README among the 135 verified inputs; all 133 others and all 254 operational evidence files '
    'remain identical. Historical phase labels, metadata snapshots and the archived statement-stage '
    'README are preserved. Relevant Tau Ceti rubrics are adapted to NLA scope; no external human '
    'review or source-author endorsement is claimed.')
manifest['review']['linux_verification']['status'] = 'passed; independently audited'
manifest['review']['linux_verification']['note'] = (
    'Actual run https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34716902324 at '
    '6a2d0868e8b7905dbd5c04d4beaae8cf43288e1f. All seven exports, 15 standard-three reports, '
    'actual default-kernel replay and both control sets passed. See '
    'verification/linux-2026-09-12/OPERATIONAL-REVIEW.md and EVIDENCE-MANIFEST.json. '
    'Original project ZIP SHA256 56172cc54a3e98496b29f46cf14d698c739f2df08883fb27cf241a4d4ac91256; '
    'control ZIP SHA256 e068281270afa36c340a6cb646d0aa711f0232b08e016356e4ad4106aa1eb57d.')
yaml_path.write_text(header + '\n' + yaml.safe_dump(manifest, sort_keys=False, allow_unicode=True, width=100))

resolved = (repo / 'RESOLVED.md').read_text()
title = '#### TR-15 — negative resolution'
assert resolved.count(title) == 1
resolved = resolved.replace(title, title + '; Lean formalization by George Stepaniants', 1)
start = resolved.index(title)
end = resolved.index('\n#### ', start + len(title))
block = resolved[start:end].rstrip() + '''

**Lean verified — 2026-09-12.** The full original inheritance conjecture is refuted, with a
proved nonvacuous lower premise, by the
[seven checked exports](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/6a2d0868e8b7905dbd5c04d4beaae8cf43288e1f/tensor-computations/TR-15/lean/Solution.lean).
**Lean formalization: George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA**, with AI-agent assistance.
Matthew J. Colbrook retains authorship of the counterexample and informal proof. See the
[canonical verification evidence](tensor-computations/TR-15/README.md#lean-proof-and-verification-evidence---2026-09-12),
[two statement and two final proof reviews](tensor-computations/TR-15/lean/reviews/),
[successful Linux run](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34716902324)
and [independent operational audit](tensor-computations/TR-15/lean/verification/linux-2026-09-12/OPERATIONAL-REVIEW.md).
All 135 submitted input hashes, default-kernel replay, standard-three axioms and actual rejection
controls were verified. No external human peer review is claimed.

'''
resolved = resolved[:start] + block + resolved[end:]
(repo / 'RESOLVED.md').write_text(resolved)
(pub / 'prepare.py').write_bytes(Path(__file__).read_bytes())
print('TR-15 publication wrappers and complete canonical evidence prepared; proofs/evidence untouched.')
