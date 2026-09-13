from pathlib import Path
from datetime import datetime, timezone
import collections
import hashlib
import json
import re
import subprocess
import yaml

repo = Path('/tmp/nla-lean-mi23-worktree')
entry = repo / 'matrix-inequalities-and-norms/MI-23'
project = entry / 'lean'
linux = project / 'verification/linux-2026-09-12'
pub = project / 'verification/publication-2026-09-12'
revision = '17194f9060609acae429e14d3dc3c4562b84f2bd'
base = 'f41f1f9ffa2171550d4bb795862c6170c4f26070'
work = Path('/tmp/nla-lean-formalization/mi23-publication')

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
target = canonical[canonical.index('## Problem statement'):]
registry = json.loads((repo / 'problem_ids.json').read_text())
counts = collections.Counter(re.search(r'^\*\*Status:\*\*\s+([^\n]+)', (repo / p).read_text(), re.M).group(1).strip() for p in registry.values())
baseline = {
    'verified_revision': revision,
    'verified_run': 34716784038,
    'base': base,
    'integrated_head': integration['integration_commit'],
    'all_verified_inputs': before_merge['verified_inputs'],
    'all_operational_evidence': before_merge['operational_files'],
    'canonical_target_tail_sha256': hashlib.sha256(target.encode()).hexdigest(),
    'other_canonical': {k: sha(repo / p) for k, p in registry.items() if k != 'MI-23'},
    'problem_ids_sha256': sha(repo / 'problem_ids.json'),
    'branch_counts_before': dict(counts),
    'created_utc': datetime.now(timezone.utc).isoformat(),
}
(pub / 'before.json').write_text(json.dumps(baseline, indent=2) + '\n')
for name in ['integration.json', 'integration.log']:
    (pub / name).write_bytes((work / name).read_bytes())

section = r'''## Lean proof and verification evidence - 2026-09-12

**The complete corrected MI-23 conjecture is false, with a Lean-verified counterexample.** The rational complex positive-definite witness has $`r=s=1`$, $`p=2`$, $`t=1/8`$ and violates the first ordered eigenvalue inequality. The [proof at revision 17194f9](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/17194f9060609acae429e14d3dc3c4562b84f2bd/matrix-inequalities-and-norms/MI-23/lean) preserves every original dimension, both real $`r,s`$ regions, actual CFC matrix powers, all proper prefix products and equality of complete products.

**Mathematical counterexample and informal proof:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance.

The eight [checked exports](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/17194f9060609acae429e14d3dc3c4562b84f2bd/matrix-inequalities-and-norms/MI-23/lean/Solution.lean), each with prefix `NLA.MI23.`, are:

- `positive_powers_and_means`: genuine CFC powers and generalized means are positive definite.
- `product_eigenvalue_semantics`: complete characteristic roots with multiplicities, positivity, ordering, similarity and determinant product.
- `squared_product_largest`: the actual largest root of $`X^2Y^2`$ equals $`\|XY\|_2^2`$.
- `operator_norm_bounds`: entry and Frobenius bounds for the genuine Euclidean operator norm.
- `witness_data`: admissibility and all actual CFC witness identities.
- `witness_squared_gap`: the exact rational gap and strict operator-norm separation.
- `counterexample`: failure of the original log-majorization relation at the admissible witness.
- `not_generalizedGeometricMeanConjecture`: negation of the complete universal conjecture.

Two independent agents reviewed the [frozen statements and completed proof](lean/reviews/). [Linux run 34716784038](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34716784038) matched all eight exports using the sandboxed Comparator and replayed the solution in Lean's default kernel. The [original artifacts and independent operational audit](lean/verification/linux-2026-09-12/) bind all 133 verified source inputs and both actual isolation and rejection-control suites. All 64 [internal/public transitive axiom reports](lean/verification/linux-2026-09-12/axiom-verification.json) contain only `propext`, `Classical.choice` and `Quot.sound`. These are independent agent reviews, without a claim of external human peer review.

The proof pins **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). Exact integer-power identities replace fractional-power approximation. One kernel-mode LeanCert certificate proves the positive rational gap and remains in the final norm and eigenvalue contradiction. See the [manifest](lean/formalization.yaml), [dependency pins](lean/lake-manifest.json) and [numerical targets](lean/NUMERICAL_TARGETS.md). From the verified revision on a documented [non-root Linux host](../../tools/lean/HARNESS.md), reproduce with:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  matrix-inequalities-and-norms/MI-23/lean \
  /absolute/path/to/nla-lean-tools
```

This settles the corrected eigenvalue conjecture stated below. The earlier singular-value conjecture is a different target. The original problem and historical informal proof remain intact.

'''
canonical = canonical.replace('**Status:** Solved  ', '**Status:** Lean verified', 1)
canonical = canonical.replace('**Last checked:** 2026-09-11', '**Last checked:** 2026-09-12', 1)
canonical = canonical.replace('## Resolution — 2026-09-11', section + '## Resolution — 2026-09-11', 1)
canonical = canonical.replace(
    'The draft was AI-assisted; this is independent agent verification, not external human peer review or formal certification.',
    'The draft was AI-assisted; the 2026-09-11 review was independent agent verification, without external human peer review or formal certification. The later Lean verification above covers the complete corrected target.', 1)
assert canonical[canonical.index('## Problem statement'):] == target
(entry / 'README.md').write_text(canonical)

readme = (project / 'README.md').read_text()
start = readme.index('The complete eight-export proof')
end = readme.index('`Challenge.lean` retains', start)
readme = readme[:start] + '''The complete corrected conjecture has a **Lean-verified negative answer** as of
12 September 2026. Its unchanged proof at
[revision 17194f9](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/17194f9060609acae429e14d3dc3c4562b84f2bd/matrix-inequalities-and-norms/MI-23/lean)
passed two independent statement reviews before implementation, two independent
final proof reviews, and actual Linux sandboxed Comparator/default-kernel
verification in [run 34716784038](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34716784038).
The [independent operational audit and original artifacts](verification/linux-2026-09-12/)
bind all eight exports and the complete 133-file verified input set. The
[canonical entry](../README.md) records the complete formal scope and status.
''' + readme[end:]
readme = readme.replace(
    '`comparator.json` reserves the eight reviewed\nexports and standard-three-axiom whitelist for later real Linux verification.',
    '`comparator.json` selected the eight reviewed exports and the standard-three-axiom\nwhitelist in the actual successful Linux verification.')
readme = readme.replace(
    'macOS checks reused the ten verified clean pinned dependency caches; they do not\nclaim full dependency-source rebuilds or an actual project-specific Linux run.',
    '''macOS checks reused the ten verified clean pinned dependency caches. The later
Linux job freshly cloned all ten dependencies at their exact revisions and used
8690 official Mathlib cache artifacts before building the project sources. It
does not claim a rebuild of every dependency from source. The actual job and
the separate checker job both passed real isolation and rejection controls;
the nested Bubblewrap probe was denied at UID-map creation before its inner
write. No general sandbox-security guarantee follows from those finite probes.''')
readme = readme.replace(
    'Only the current README changes among the 25 proof-freeze inputs; the remaining\n24 and all prior reviews/evidence are preserved during packaging.',
    '''At candidate packaging, only the current README changed among the 25
proof-freeze inputs. Publication changes only this README and the current
formalization manifest among the 133 Linux-verified inputs; the other 131,
including every mathematical source, configuration, dependency pin and prior
review, remain byte-identical. All 249 retained Linux evidence files are
unchanged, including their historical metadata snapshots. The successful run
is bound to the immutable proof revision, rather than claimed as a new run
over these publication wrappers.''')
readme = readme.replace('independent agent review and eventual mechanical verification remain',
                        'independent agent review and mechanical verification remain')
readme += '''
The full [Linux evidence manifest](verification/linux-2026-09-12/EVIDENCE-MANIFEST.json)
retains both original ZIPs, raw logs, all input hashes, checked tool sources and
the independent operational report. From the immutable verified revision on a
documented [non-root Linux host](../../../tools/lean/HARNESS.md), run:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \\
  matrix-inequalities-and-norms/MI-23/lean \\
  /absolute/path/to/nla-lean-tools
```
'''
(project / 'README.md').write_text(readme)

yaml_path = project / 'formalization.yaml'
header = yaml_path.read_text().splitlines()[0]
manifest = yaml.safe_load(yaml_path.read_text())
manifest['status']['scope'] = (
    'Complete negative answer to canonical MI-23, with every original complex PD and real-parameter '
    'quantifier preserved. All eight exports passed two independent statement reviews, two independent '
    'final proof reviews and actual Linux sandboxed Comparator/default-kernel verification in run '
    '34716784038 on 2026-09-12 at unchanged proof revision 17194f9060609acae429e14d3dc3c4562b84f2bd. '
    'The independent operational audit binds all 133 input files, original artifact digests and both '
    'actual isolation/rejection-control suites. Canonical status is Lean verified.')
manifest['review']['status'] = 'agent-reviewed; Linux-Comparator-and-default-kernel-verified'
manifest['review']['notes'] = (
    'Both statement approvals precede implementation and bind unchanged definitions, Challenge and '
    'numerical targets. Both final referees freshly re-elaborated the actual proof in separate object '
    'prefixes and inspected complete matrix/CFC/spectral semantics and certificate consumption. '
    'The eight intentional Challenge placeholders remain isolated. All 64 distinct implementation/public '
    'axiom reports contain exactly propext, Classical.choice and Quot.sound; all kernel trust checks '
    'passed. The single kernel-mode LeanCert point certificate remains in the complete negation. '
    'Local macOS checks used exact clean dependency caches. Actual Linux run 34716784038 at revision '
    '17194f9060609acae429e14d3dc3c4562b84f2bd matched all eight exports, replayed the solution through '
    'the default kernel, and passed both real control sets. Independent agent /root/leancert_examples '
    'audited all original ZIP bytes, raw logs, 133 input hashes, ten fresh dependency clones and 8690 '
    'official Mathlib cache artifacts. No full dependency-source rebuild is claimed. The nested Bubblewrap '
    'probe was denied at UID-map creation before its inner write. The operational report SHA256 is '
    '1139c7f2f075021479dbd4501e2530859e9724e87ba52e7551970e38882eaeec, and the outer evidence manifest is '
    '9d75182ae4c4afa2e218490ec13406096b0ff3f288d79a98584e7045fc63e37e, binding 248 files plus itself. '
    'Publication changes only this manifest and the project README among the 133 verified inputs; '
    'all 131 other inputs and all 249 operational evidence files remain identical. Historical metadata '
    'and review-stage labels remain preserved in their snapshots. The original frozen README remains '
    'archived. The pinned Tau Ceti rubrics are adapted to NLA scope; no external human review or '
    'source-author endorsement is claimed.')
manifest['review']['linux_verification']['status'] = 'passed; independently audited'
manifest['review']['linux_verification']['note'] = (
    'Actual run https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34716784038 at '
    '17194f9060609acae429e14d3dc3c4562b84f2bd. Eight exports, 64 standard-three reports, actual kernel '
    'replay and both control sets passed. See verification/linux-2026-09-12/OPERATIONAL-REVIEW.md '
    'and EVIDENCE-MANIFEST.json. Original project ZIP SHA256 '
    '9a7fad97c70da8ebcdca8880017a045ca6bd997118c23a44c4b652c79d3c4d2a; control ZIP SHA256 '
    '0c607888bd0d8bbaa903c75820f138056834a9f0c4adb2c27bb14122e8e120ee.')
yaml_path.write_text(header + '\n' + yaml.safe_dump(manifest, sort_keys=False, allow_unicode=True, width=100))

resolved = (repo / 'RESOLVED.md').read_text()
title = '#### MI-23 — negative result'
assert resolved.count(title) == 1
resolved = resolved.replace(title, title + '; Lean formalization by George Stepaniants', 1)
start = resolved.index(title)
end = resolved.index('\n#### ', start + len(title))
block = resolved[start:end].rstrip() + '''

**Lean verified — 2026-09-12.** The complete corrected eigenvalue conjecture is refuted by the
[eight checked exports](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/17194f9060609acae429e14d3dc3c4562b84f2bd/matrix-inequalities-and-norms/MI-23/lean/Solution.lean).
**Lean formalization: George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA**, with AI-agent assistance.
Matthew J. Colbrook retains authorship of the counterexample and informal proof. See the
[canonical verification evidence](matrix-inequalities-and-norms/MI-23/README.md#lean-proof-and-verification-evidence---2026-09-12),
[two statement and two final proof reviews](matrix-inequalities-and-norms/MI-23/lean/reviews/),
[successful Linux run](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34716784038)
and [independent operational audit](matrix-inequalities-and-norms/MI-23/lean/verification/linux-2026-09-12/OPERATIONAL-REVIEW.md).
All 133 submitted input hashes, default-kernel replay, standard-three axioms and actual rejection
controls were verified. No external human peer review is claimed.

'''
resolved = resolved[:start] + block + resolved[end:]
(repo / 'RESOLVED.md').write_text(resolved)
(pub / 'prepare.py').write_bytes(Path(__file__).read_bytes())
print('MI-23 wrappers and canonical evidence prepared; immutable proofs/evidence untouched.')
