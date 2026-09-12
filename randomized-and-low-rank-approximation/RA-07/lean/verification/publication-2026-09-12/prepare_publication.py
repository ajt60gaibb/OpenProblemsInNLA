from pathlib import Path
import collections
import datetime
import hashlib
import json
import re
import subprocess
import yaml

repo = Path('/tmp/nla-lean-ra07-worktree')
rel = Path('randomized-and-low-rank-approximation/RA-07')
entry = repo / rel
project = entry / 'lean'
linux = project / 'verification/linux-2026-09-12'
publication = project / 'verification/publication-2026-09-12'
revision = 'bf144a8ea84992d64f79f4425b18352843376286'
base = 'c0601d8825e9f9e744212c62e6a43fefc1c60a22'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def git(*args):
    return subprocess.check_output(['git', *args], cwd=repo)

assert git('rev-parse', 'nla-upstream/main').decode().strip() == base
assert subprocess.run(['git', 'merge-base', '--is-ancestor', base, 'HEAD'], cwd=repo).returncode == 0
assert not (publication / 'before.json').exists(), 'Do not overwrite publication baseline'
assert sha(linux / 'OPERATIONAL-REVIEW.md') == '13b7c580ce72e1778366fbfb55e9276428cea6b803587409dd9c4dca551654a8'
assert sha(linux / 'EVIDENCE-MANIFEST.json') == 'd3d823f86c97f236bdf31b96aff2c1fe6ea0a7ba2afa4995fd7d6b7e5ea870d8'
evidence = json.loads((linux / 'EVIDENCE-MANIFEST.json').read_text())
assert len(evidence['files']) == 237
for name, record in evidence['files'].items():
    assert sha(linux / name) == record['sha256']
    assert (linux / name).stat().st_size == record['bytes']
receipt_rel = Path('artifacts/lean-RA-07/verify-20260912T195642Z-4213/result.json')
receipt = json.loads((linux / receipt_rel).read_text())
assert receipt['repository_commit'] == revision
assert receipt['result'] == 'comparator-accepted'
assert len(receipt['input_sha256']) == 123
for name, expected in receipt['input_sha256'].items():
    assert sha(project / name) == expected, name

canonical = (entry / 'README.md').read_text()
target_marker = 'For $`n\\geq3`$ and positive real numbers'
source_tail = canonical[canonical.index(target_marker):]
registry = json.loads((repo / 'problem_ids.json').read_text())
assert len(registry) == 217
prior = [(ident, path) for ident, path in registry.items()
         if '**Status:** Lean verified' in (repo / path).read_text()]
protected = ['NLA/RA07/Definitions.lean', 'NLA/RA07/Algebra.lean',
             'NLA/RA07/Roots.lean', 'NLA/RA07/Sums.lean', 'NLA/RA07/Proof.lean',
             'Challenge.lean', 'Solution.lean', 'NUMERICAL_TARGETS.md', 'SOURCE_MAP.md',
             'comparator.json', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json']
reviews = ['statement-referee-1.md', 'statement-referee-2.md',
           'proof-referee-1.md', 'proof-referee-2.md']
source_paths = [
    'references/colbrook-transfer-2026-09-11/manuscripts/01_volume_sampling_convexity.tex',
    'references/colbrook-transfer-2026-09-11/manuscripts/01_volume_sampling_convexity.pdf',
    'references/colbrook-transfer-2026-09-11/manuscripts/01_volume_sampling_convexity.md',
    'references/colbrook-transfer-2026-09-11/verification/reviews/RA-07-review.md',
]
status_counts = collections.Counter(
    re.search(r'^\*\*Status:\*\*\s+([^\n]+)', (repo / path).read_text(), re.M).group(1).strip()
    for path in registry.values())
before = {
    'verified_revision': revision,
    'verified_run': 34715563781,
    'upstream_base': base,
    'integrated_head': git('rev-parse', 'HEAD').decode().strip(),
    'receipt': str(receipt_rel),
    'protected': {name: sha(project / name) for name in protected},
    'reviews': {name: sha(project / 'reviews' / name) for name in reviews},
    'all_verified_inputs': receipt['input_sha256'],
    'operational_evidence': {name: sha(linux / name)
                             for name in [*evidence['files'], 'EVIDENCE-MANIFEST.json']},
    'canonical_target_tail_sha256': hashlib.sha256(source_tail.encode()).hexdigest(),
    'original_informal_files': {name: sha(repo / name) for name in source_paths},
    'other_canonical': {ident: sha(repo / path) for ident, path in registry.items() if ident != 'RA-07'},
    'prior_lean_verified': prior,
    'branch_counts_before': dict(status_counts),
    'problem_ids_sha256': sha(repo / 'problem_ids.json'),
    'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
}
publication.mkdir(parents=True, exist_ok=True)
(publication / 'before.json').write_text(json.dumps(before, indent=2) + '\n')

section = r'''## Lean proof and verification evidence — 2026-09-12

**The complete original discrete-convexity assertion is Lean verified.** For every $`n\geq3`$, every strictly positive real tuple and every $`2\leq j\leq n-1`$, the actual elementary-symmetric ratios satisfy $`f(j-1)-2f(j)+f(j+1)\geq0`$. The [proof at revision bf144a8](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/bf144a8ea84992d64f79f4425b18352843376286/randomized-and-low-rank-approximation/RA-07/lean) includes repeated eigenvalues and both endpoint indices, with no ordering or factorization assumption.

**Mathematical proof:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance.

The proof derives the full-multiplicity positive-factor representation of the actual generating-polynomial derivative of order $`j-1`$. For its $`n-j+1\geq2`$ factors $`\mu_a>0`$, it proves the exact certificate

```math
f(j-1)-2f(j)+f(j+1)
=\frac{2\sum_{a<b}\mu_a\mu_b(\mu_a-\mu_b)^2}
{s_1(s_1^2-s_2)}\geq0,
\qquad s_r=\sum_a\mu_a^r,
```

including strict positivity of the denominator. The six [checked exports](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/bf144a8ea84992d64f79f4425b18352843376286/randomized-and-low-rank-approximation/RA-07/lean/Solution.lean), each with prefix `NLA.RA07.`, are:

- `elementary_values`: actual subset-sum conventions and positivity.
- `generating_derivative_values`: actual coefficients and factorial-scaled derivatives.
- `positive_derivative_factorization`: exact degree, real splitting and every root multiplicity.
- `power_sum_certificate`: positive denominator and exact nonnegative pair identity.
- `second_difference_certificate`: that identity for every original ratio and index.
- `errorSequence_convex`: the complete affirmative canonical theorem.

Two independent agents reviewed the [statements](lean/reviews/statement-referee-1.md), [second statement report](lean/reviews/statement-referee-2.md), [completed proof](lean/reviews/proof-referee-1.md) and [second proof report](lean/reviews/proof-referee-2.md). [Linux run 34715563781](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34715563781) compared all six exports with the sandboxed Comparator and replayed the solution in Lean's default kernel. The [independent operational audit and original artifacts](lean/verification/linux-2026-09-12/) bind all 123 verified inputs and the actual isolation and rejection controls. Twelve internal/public transitive axiom checks use only `propext`, `Classical.choice` and `Quot.sound`. These are independent agent reviews, without a claim of external human peer review.

The proof pins **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). LeanCert audits kernel trust for exact algebra and root geometry; this proof has no numerical interval certificate or approximate root computation. See the [manifest](lean/formalization.yaml), [dependency pins](lean/lake-manifest.json) and [exact targets](lean/NUMERICAL_TARGETS.md). From the verified revision on a documented [non-root Linux host](../../tools/lean/HARNESS.md), reproduce with:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  randomized-and-low-rank-approximation/RA-07/lean \
  /absolute/path/to/nla-lean-tools
```

The source's additional monotonicity, index-one, sampling-expectation and application claims are outside these six exports. The complete original scalar convexity target and its historical informal proof remain below.

'''
canonical = canonical.replace('**Status:** Solved  ', '**Status:** Lean verified', 1)
canonical = canonical.replace('**Last checked:** 2026-09-11  ', '**Last checked:** 2026-09-12', 1)
canonical = canonical.replace('<!-- colbrook-transfer -->', section + '<!-- colbrook-transfer -->', 1)
canonical = canonical.replace(
    'Verification is independent agent review, not external human peer review or formal certification.',
    'The 2026-09-11 verification was independent agent review, without external human peer review or formal certification. The later Lean verification above covers the complete canonical scalar convexity target.', 1)
assert canonical[canonical.index(target_marker):] == source_tail
(entry / 'README.md').write_text(canonical)

readme = (project / 'README.md').read_text()
start = readme.index('The complete original discrete-convexity theorem')
end = readme.index('\nFormalization:', start)
readme = readme[:start] + '''The complete original discrete-convexity theorem is **Lean verified** as of
12 September 2026. Its unchanged proof at
[revision bf144a8](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/bf144a8ea84992d64f79f4425b18352843376286/randomized-and-low-rank-approximation/RA-07/lean)
passed two independent statement reviews, two independent final proof reviews,
and actual sandboxed Linux Comparator/default-kernel verification in
[run 34715563781](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34715563781).
The [independent operational audit and original artifacts](verification/linux-2026-09-12/)
bind all six exports and the complete 123-file verified input set.
''' + readme[end:]
readme = readme.replace(
    'These checks used fresh target artifacts on macOS and matching dependency\ncaches at ten verified clean pins. They are not the pending Linux operational\ncheck or a claim that all dependency sources were rebuilt.',
    '''The local referee checks used fresh target artifacts on macOS and matching
dependency caches at ten verified clean pins. The later authoritative Linux run
cloned all ten dependencies at their exact revisions and downloaded/decompressed
8690 official Mathlib cache files before building the RA-07 sources. No user
project build cache was reused; this is not a claim that every dependency module
was rebuilt from source.''')
readme = readme.replace('## Reproduction and remaining gate', '## Reproduction and actual Linux evidence')
readme = readme.replace(
    "After the candidate has an immutable Git revision, the repository's\n[shared Linux workflow](../../../docs/lean/README.md) must build and export\nboth environments, compare all six statements, replay them in Lean's default\nkernel, and run the real isolation/rejection controls. From a correctly\nconfigured non-root Linux checkout, run these shared commands from the repository root:",
    """The repository's [shared Linux workflow](../../../docs/lean/README.md) built
and exported both environments, compared all six statements, replayed the
solution in Lean's default kernel, and ran the real isolation/rejection controls.
From the immutable verified revision on a correctly configured non-root Linux
host, run these shared commands from the repository root:""")
readme = readme.replace(
    'Those commands have **not run for this RA-07 candidate**. Their successful\nartifacts need an independent operational audit before catalog promotion.',
    '''The actual RA-07 job and the separate checker job both passed. Their original
ZIPs, raw logs, complete verified sources, exact input/tool hashes and independent
audit are retained in [the Linux evidence directory](verification/linux-2026-09-12/),
bound by its [evidence manifest](verification/linux-2026-09-12/EVIDENCE-MANIFEST.json).
The operational report distinguishes the observed controls precisely: the nested
bubblewrap executable ran, but UID-map creation was denied before its inner write.
No general sandbox-security guarantee is inferred from those finite controls.''')
readme = readme.replace(
    'Only this current README changes among the 38 proof-freeze inputs; all 37\nremaining inputs, mathematical files, configuration, prior review evidence\nand canonical sources remain unchanged. The current README and manifest\nreport the completed local gates and the pending Linux gate.',
    '''The original candidate had changed only its current README among the 38
proof-freeze inputs. Publication now changes only this README and the current
formalization manifest among the 123 Linux-verified inputs; all other 121,
including every mathematical file, configuration, pin and prior review, remain
byte-identical. All 238 retained Linux evidence files are unchanged. Their source
snapshots retain the then-pending metadata: the successful run is bound to the
immutable proof revision and is not represented as a new run over these updated
publication wrappers. The canonical original target and Colbrook source files
remain unchanged.''')
(project / 'README.md').write_text(readme)

manifest = yaml.safe_load((project / 'formalization.yaml').read_text())
manifest['status']['scope'] = (
    'Complete affirmative answer to the original canonical RA-07 scalar convexity question. '
    'All six exports passed local Lean elaboration, standard-three transitive axiom and kernel-trust checks, '
    'two independent statement reviews and two independent final proof reviews. The unchanged proof at '
    'revision bf144a8ea84992d64f79f4425b18352843376286 passed actual non-root Linux sandboxed Comparator, '
    'separate default-kernel replay and isolation/rejection controls in run 34715563781 on 2026-09-12. '
    'An independent operational audit binds all 123 input files and original artifact digests. Canonical '
    'status is Lean verified. The source’s additional sampling and monotonicity results are outside '
    'these six formal exports. LeanCert supplies kernel trust auditing; no numerical interval certificate is claimed.')
manifest['review']['status'] = 'agent-reviewed; Linux-Comparator-and-default-kernel-verified'
manifest['review']['notes'] = (
    'Both statement approvals precede implementation and bind unchanged mathematical definitions, Challenge '
    'and numerical targets. Both final referees freshly re-elaborated the actual implementation in separate '
    'artifact prefixes and inspected the complete proof, actual Mathlib semantics and retained mathematical '
    'dependencies. Twelve distinct source declarations pass kernel trust assertions and have exactly the three '
    'standard axioms; independent inspections repeat the six public checks. The six deliberate Challenge '
    'placeholders are isolated and excluded from proof-development sorry counts. Local macOS checks reused '
    'dependency artifacts at ten verified clean pins. Actual Linux run 34715563781 at revision '
    'bf144a8ea84992d64f79f4425b18352843376286 passed all six comparisons, default-kernel replay and both '
    'observed control sets. Independent agent /root/formal_review_standards audited complete original ZIPs, '
    'raw logs, every one of the 123 inputs, ten fresh dependency clones with 8690 official Mathlib cache files, '
    'and the exact pinned tools. The nested bubblewrap probe was denied at UID-map creation before its inner '
    'write; no general sandbox-security guarantee is claimed. No interval certificate or full dependency-source '
    'rebuild is claimed. The pinned Tau Ceti rubrics were adapted to the complete canonical target. Historical '
    'freeze/review records retain their phase labels and hashes; the old statement-stage README remains at '
    'verification/linux-candidate-2026-09-12/frozen-statement-stage-README.md. Publication changes only the '
    'current README and this manifest among the 123 verified inputs; all remaining 121 and all 238 retained '
    'Linux evidence files remain byte-identical. Original snapshots retain historical pending metadata. '
    'No external human peer review or source-author endorsement is claimed.')
manifest['review']['linux_verification']['status'] = 'verified'
manifest['review']['linux_verification']['note'] = (
    'Run https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34715563781 at immutable revision '
    'bf144a8ea84992d64f79f4425b18352843376286 succeeded. Independent audit: '
    'verification/linux-2026-09-12/OPERATIONAL-REVIEW.md (SHA256 '
    '13b7c580ce72e1778366fbfb55e9276428cea6b803587409dd9c4dca551654a8). '
    'EVIDENCE-MANIFEST.json SHA256 d3d823f86c97f236bdf31b96aff2c1fe6ea0a7ba2afa4995fd7d6b7e5ea870d8 '
    'binds 237 files plus the manifest itself. Original RA-07 ZIP SHA256 '
    '6dc4290003ad74023d07c6d174cabf322b0fa5d0d4cec079cee56f6a61a1bd92; checker ZIP SHA256 '
    'cd5cdf75cb93cce76a00b2e6b5c922ed32e2e9c6f5d64330b82c5b8d47cd2b1d. '
    'All six selected statements matched and the proof replayed in Lean’s default kernel; semantic fidelity '
    'is supplied separately by the two independent final proof reviews.')
schema = '# yaml-language-server: $schema=https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/99c678e569c7c4c0772db297c5ddd5e4c9b6322e/schema/v0.4.schema.json\n'
(project / 'formalization.yaml').write_text(schema + yaml.safe_dump(manifest, sort_keys=False, allow_unicode=True, width=100))

resolved = (repo / 'RESOLVED.md').read_text()
line = next(line for line in resolved.splitlines() if line.startswith('**RA-07 (Solved).**'))
new_line = line.replace('**RA-07 (Solved).**', '**RA-07 (Lean verified; formalization by George Stepaniants).**', 1)
new_line += (' **Lean verification — 2026-09-12:** George Stepaniants, Department of Computing and Mathematical '
    'Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. '
    'Matthew J. Colbrook retains mathematical authorship. The six [formal exports]'
    '(randomized-and-low-rank-approximation/RA-07/lean/Solution.lean) prove the complete original scalar '
    'convexity target for every positive spectrum and every canonical index; the source’s additional '
    'monotonicity and sampling applications are outside their scope. Two independent statement reviews, '
    'two independent final proof reviews and [Linux run 34715563781]'
    '(https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34715563781) verify the unchanged '
    'proof at [revision bf144a8]'
    '(https://github.com/sgstepaniants/OpenProblemsInNLA/tree/bf144a8ea84992d64f79f4425b18352843376286/randomized-and-low-rank-approximation/RA-07/lean); '
    '[original evidence and independent operational audit]'
    '(randomized-and-low-rank-approximation/RA-07/lean/verification/linux-2026-09-12/) are retained. '
    'LeanCert audits kernel trust for this exact proof, without a numerical interval certificate.')
assert resolved.count(line) == 1
(repo / 'RESOLVED.md').write_text(resolved.replace(line, new_line, 1))
for name, expected in before['protected'].items():
    assert sha(project / name) == expected
for name, expected in before['reviews'].items():
    assert sha(project / 'reviews' / name) == expected
print(json.dumps({'publication_prepared': True, 'verified_revision': revision,
                  'base': base, 'counts_before': dict(status_counts),
                  'preserved_other_inputs': 121, 'linux_evidence_files': 238}, indent=2))
