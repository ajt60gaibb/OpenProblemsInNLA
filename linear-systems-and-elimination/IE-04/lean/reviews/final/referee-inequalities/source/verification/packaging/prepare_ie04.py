#!/usr/bin/env python3
"""Metadata/evidence packaging only. Never invokes Lean, Lake or Git mutations."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import yaml

BASE = Path('/tmp/nla-lean-next-20260915')
AUTHOR = BASE / 'elimination/IE-04'
PROJECT = Path('/private/tmp/nla-lean-next-ie04-worktree/linear-systems-and-elimination/IE-04/lean')
SOURCE_REVIEW = BASE / 'reviews/IE04-inequalities-full-source-referee'
RUN = BASE / 'development-runs/35031607095'
COMMIT = '4bd2d76ec6e37696ff0c2d5feacf21e342371f27'


def sha(b):
    return hashlib.sha256(b).hexdigest()


def write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + '.tmp')
    with tmp.open('w') as f:
        f.write(text)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)


def json_write(path, data):
    write(path, json.dumps(data, indent=2, ensure_ascii=False) + '\n')


def copy(src, dst):
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(src, dst)


assert not PROJECT.exists(), 'Refuse to overwrite an existing package'
PROJECT.mkdir(parents=True)
approved = json.loads((SOURCE_REVIEW / 'INPUTS.json').read_text())['source_files']
for rel, expected in approved.items():
    assert sha((AUTHOR / rel).read_bytes()) == expected, ('unreviewed author edit', rel)
    copy(AUTHOR / rel, PROJECT / rel)
copy(AUTHOR / 'LICENSE', PROJECT / 'LICENSE')
write(PROJECT / '.gitignore', '.lake/\n*.olean\n*.ilean\n')

# Preserve the exact freeze and statement-era dependency/configuration boundary.
frozen = ['NLA/IE04/Definitions.lean', 'Challenge.lean', 'NUMERICAL_TARGETS.md',
          'comparator.json', 'STATEMENT-FREEZE.json', 'lakefile.toml',
          'lake-manifest.json', 'lean-toolchain', 'LICENSE']
for rel in frozen:
    copy(AUTHOR / rel, PROJECT / 'reviews/statement-phase/frozen' / rel)
for src, dst in [
    (BASE / 'reviews/IE04-root-statements', PROJECT / 'reviews/statements/referee-root'),
    (BASE / 'reviews/IE04-inequalities-statement', PROJECT / 'reviews/statements/referee-inequalities'),
    (BASE / 'reviews/IE04-root-source', PROJECT / 'reviews/proof-source/referee-root'),
    (SOURCE_REVIEW, PROJECT / 'reviews/proof-source/referee-inequalities'),
]:
    shutil.copytree(src, dst)

# Keep actual failed-aggregate evidence intact: the IE04 complete command passed.
shutil.copytree(RUN, PROJECT / 'verification/development-2026-09-15')
before = PROJECT / 'verification/packaging/before'
for rel in ['README.md', 'formalization.yaml', 'lakefile.toml', 'SourceCorrespondence.md']:
    copy(AUTHOR / rel, before / rel)

# Only package configuration changes; the proof and pins remain byte-identical.
lake = (AUTHOR / 'lakefile.toml').read_text()
assert lake.count('defaultTargets = ["Challenge"]') == 1
lake = lake.replace('defaultTargets = ["Challenge"]', 'defaultTargets = ["Solution"]')
assert 'name = "Solution"' not in lake
write(PROJECT / 'lakefile.toml', lake.rstrip() + '\n\n[[lean_lib]]\nname = "Solution"\n')

readme = '''# IE-04 Lean formalization

George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
AI-assisted mathematical solution and formalization. Historical conjecture
credit remains with Spielman and Teng.

**The complete proof graph has compiled; canonical verification is pending.**
All 21 frozen targets passed the actual non-root Linux development command
`lake build NLA.IE04.Solution` in
[run 35031607095](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35031607095/job/104591152756)
at Git revision `4bd2d76ec6e37696ff0c2d5feacf21e342371f27`.
Every target passed its LeanCert kernel assertion and reported only `propext`,
`Classical.choice` and `Quot.sound`. This package preserves those exact proof
bytes. The overall shared workflow failed in the separate unfinished MF-12
project; its original receipt and logs are retained without relabeling it.

The result proves the full negative resolution: no universal positive real
constants give the proposed exponential tail for Gaussian-smoothed partial
pivoting. It uses the actual GEPP trajectory and entry-growth maximum, genuine
independent standard Gaussian entries, every admissible tie rule, a whole
nonsingular perturbation box, and arbitrary positive real proposed constants.
The allowed identity center and noise scale one already give the contradiction.
No behavior on singular inputs is used to manufacture a counterexample.

The only numerical certificate is the fixed inequality `exp(-2)>1/8`, checked
by LeanCert in kernel mode. Exact scalar estimates, symbolic induction,
monotonicity and product measures remove any need for high-dimensional interval
subdivision, sampling, or numerical integration.

From this directory, with the pinned Lean toolchain available:

```bash
lake exe cache get
lake build +Solution
```

The default `lake build` also selects Solution. This is a package-configuration
transition from the statement phase; it changes no mathematical declaration
or dependency revision. A build alone does not run the repository's stronger
[canonical verification protocol](../../../docs/lean/README.md).

[Challenge.lean](Challenge.lean) contains the 21 independent frozen statement
contracts with deliberate placeholder bodies. [Solution.lean](Solution.lean)
imports the proved graph, never Challenge. The exact numerical statements,
definitions and contracts were reviewed by two independent agents and
successfully elaborated on Linux before proof construction. Their original
draft labels and source bytes are retained in
[the frozen statement record](reviews/statement-phase/frozen).

[Both mathematical source reviews](reviews/proof-source) and the
[independent development-evidence addendum](reviews/proof-source/referee-inequalities/development35031607095-addendum/REVIEW.md)
are retained. The root referee's earlier full-source report retains its original
snapshot; final accepted-byte reconciliation by both referees is still required.
These are AI-agent reviews under scoped Tau Ceti standards, not official
certification or external human peer review.

[SourceCorrespondence.md](SourceCorrespondence.md) explains the whole original
target and prior IE-05 API reuse. [formalization.yaml](formalization.yaml)
records every target and its current status;
[ACTIVE-SOURCE-MANIFEST.json](ACTIVE-SOURCE-MANIFEST.json) binds the compiled
mathematical bytes. The [raw development evidence](verification/development-2026-09-15)
and [packaging transition](verification/packaging) distinguish the tested
development revision from this new standalone candidate.

Actual canonical Comparator, independent default-kernel replay, required
negative controls and final source/evidence referee acceptance remain pending.
The canonical problem status and indexes have not been changed by this package.
'''
write(PROJECT / 'README.md', readme)

correspondence = (AUTHOR / 'SourceCorrespondence.md').read_text()
prefix, tail = correspondence.split('All 21 frozen obligations now have candidate proofs.', 1)
write(PROJECT / 'SourceCorrespondence.md', prefix + '''All 21 frozen obligations passed the complete actual non-root Linux development
build in run 35031607095 at commit 4bd2d76ec6e37696ff0c2d5feacf21e342371f27.
The current standalone mathematical files are byte-identical to those accepted
inputs. Each Solution export passed its LeanCert kernel assertion and printed
only propext, Classical.choice and Quot.sound. The aggregate shared run failed
in the separate MF-12 project; the complete original receipt is retained.
The Definitions and independent Challenge had already passed Linux elaboration
after two independent statement approvals; STATEMENT-FREEZE.json is unchanged.

Two complete mathematical source reports and the current independent
source/development addendum are retained under reviews/. The root report names
its earlier snapshot; final reconciliation by both referees remains pending.
The historical candidate documentation is preserved under
verification/packaging/before/. Preparing metadata and the standalone Lake
target is a packaging contribution distinct from independent proof review.

Complete development compilation is not final canonical verification. Actual
canonical Comparator and independent default-kernel replay with rejection
controls, plus two final source/evidence addenda, remain necessary before
publication acceptance or a verified count. Adapted Tau Ceti review angles are
mathematical scope, correctness, useful source reuse and clarity; this is not
an official Tau Ceti certification-service claim. Optional source corollaries
remain outside the claimed scope and do not replace the canonical negation.
''')

metadata = yaml.safe_load((AUTHOR / 'formalization.yaml').read_text())
metadata['project']['description'] = (
    'Complete negative resolution of the uniform exponential Gaussian-smoothed GEPP tail. '
    'All 21 frozen obligations and the complete proof graph compiled successfully in the '
    'source-matched non-root Linux development run35031607095. Canonical Comparator and '
    'independent default-kernel verification remain pending.')
metadata['automation']['notes'] = (
    'Substantial AI assistance. Implementation by Codex agent /root/next_elimination. '
    'Independent mathematical source reviewers /root and /root/next_inequalities did not '
    'implement the IE-04 proofs. The inequalities referee also prepared this metadata and '
    'standalone package after source/development acceptance, a separate contribution requiring '
    'coordinator review. No local Lean or Lake execution was used. No external human peer '
    'review, official Tau Ceti certification, or final canonical verification is claimed.')
status = metadata['status']
status['whole_problem_verified'] = False
status['whole_graph_compiled'] = True
status['sorry_count'] = 0
status['sorry_in_definitions'] = 0
status['axioms'] = ['propext', 'Classical.choice', 'Quot.sound']
for result in status['main_results']:
    result['sorry_count'] = 0
    result['axioms'] = ['propext', 'Classical.choice', 'Quot.sound']
    result['verification_status'] = (
        'Actual complete source-matched Linux development build and LeanCert kernel assertion '
        'accepted; canonical Comparator/default-kernel/negative-control checks pending.')
metadata['review']['status'] = (
    'Two independent complete mathematical source reviews retained; current-source and actual '
    'development evidence accepted by the inequalities referee. Both final canonical '
    'source/runtime addenda and packaging review remain pending.')
metadata['review']['reviewers'] = [
    'OpenAI Codex agent /root: independent mathematical source referee and coordinator',
    'OpenAI Codex agent /root/next_inequalities: independent mathematical source and development-evidence referee; later metadata/package preparer',
]
metadata['review']['notes'] = (
    'Independent statement approvals and actual Linux declaration elaboration preceded the '
    'immutable freeze. Both full source reports are retained with their exact input hashes; '
    'the root report identifies its pre-repair snapshot. The inequalities addendum independently '
    'matches every accepted current source, all 115 shared Git inputs, nine command logs, '
    'before/after hashes and 21 standard-axiom target reports. Canonical final-byte reconciliation '
    'by both referees remains pending. An implementer is not counted as its own referee.')
metadata['alignment'] = {
    'source_correspondence': 'SourceCorrespondence.md', 'numerical_boundary': 'NUMERICAL_TARGETS.md',
    'frozen_statements': 'Challenge.lean', 'implementation_entry': 'Solution.lean',
    'statement_freeze': 'STATEMENT-FREEZE.json',
}
metadata['verification'].update({
    'whole_problem_verified': False, 'whole_graph_compiled': True,
    'development_run': 'https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35031607095',
    'development_commit': COMMIT,
    'development_job': 'https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35031607095/job/104591152756',
    'development_scope': 'Both IE04 proof/Challenge commands passed; aggregate job failed on MF12 only.',
    'evidence': 'verification/development-2026-09-15',
    'comparator': 'pending', 'default_kernel': 'pending', 'negative_controls': 'pending',
    'source_development_referee': 'reviews/proof-source/referee-inequalities/development35031607095-addendum/REVIEW.md',
    'note': ('Zero proof-development sorry counts and listed axiom closures describe the actual '
             'accepted solution graph. Deliberate independent Challenge placeholders and frozen '
             'historical copies are excluded and never imported by Solution. The accepted '
             'development revision is not this new standalone package revision; canonical checks '
             'must run separately on the latter.'),
})
write(PROJECT / 'formalization.yaml',
      '# yaml-language-server: $schema=../../../docs/lean/schema/v0.4.schema.json\n' +
      yaml.safe_dump(metadata, sort_keys=False, allow_unicode=True, width=100))

# Binding and explicit role separation; do not assert unperformed canonical gates.
mathematical = {rel: expected for rel, expected in approved.items()
                if rel.endswith('.lean') or rel in ['NUMERICAL_TARGETS.md','comparator.json','STATEMENT-FREEZE.json']}
for rel, expected in mathematical.items():
    assert sha((PROJECT / rel).read_bytes()) == expected
json_write(PROJECT / 'ACTIVE-SOURCE-MANIFEST.json', {
    'development_commit': COMMIT, 'development_run': 35031607095,
    'mathematical_source_sha256': mathematical,
    'whole_graph_compiled': True, 'whole_problem_verified': False,
    'canonical_comparator': 'pending', 'canonical_default_kernel': 'pending',
    'configuration_delta': 'Select Solution as default target and register its root Lean library; dependency pins and mathematical files unchanged.',
})
transition = {
    'role': 'metadata and evidence packaging by /root/next_inequalities after independent mathematical review',
    'author_tree_unchanged': True, 'proof_definition_signature_edits': False,
    'upstream_base': 'd8c38a795876b132c90df8d1be8682d3dcde394c',
    'development_commit': COMMIT, 'development_run': 35031607095,
    'canonical_status_or_index_changes': False, 'git_commit_or_push_performed': False,
    'local_Lean_or_Lake_invoked': False, 'coordinator_packaging_review': 'pending',
    'metadata_changes': [],
    'source_reviews': {
        'root': sha((PROJECT/'reviews/proof-source/referee-root/REVIEW.md').read_bytes()),
        'inequalities': sha((PROJECT/'reviews/proof-source/referee-inequalities/REVIEW.md').read_bytes()),
        'inequalities_development_addendum': sha((PROJECT/'reviews/proof-source/referee-inequalities/development35031607095-addendum/REVIEW.md').read_bytes()),
    },
}
for rel in ['README.md','formalization.yaml','lakefile.toml','SourceCorrespondence.md']:
    transition['metadata_changes'].append({'path':rel,'before_sha256':sha((before/rel).read_bytes()),
                                           'after_sha256':sha((PROJECT/rel).read_bytes())})
json_write(PROJECT/'verification/packaging/TRANSITION.json',transition)
write(PROJECT/'verification/packaging/README.md', '''# Standalone package transition

The inequalities agent prepared this isolated IE-04 package after completing
an independent review of the mathematical source and its actual development
acceptance. This later metadata/evidence work is a separate contribution. The
coordinator must review it; the preparer does not certify their own packaging.

Every active proof, definition, Challenge signature, numerical statement and
freeze remains byte-identical to the accepted private project. The original
metadata is retained in before/. Changes select Solution as the default Lake
target, register its root library, describe the observed complete development
acceptance, and preserve the distinction from pending canonical gates. Exact
before/after hashes and unchanged mathematical hashes are recorded separately.

No problem README, source solution, permanent ID, status or index is changed.
No local Lean/Lake build, dependency download, commit or push was performed by
the packager. This package still needs the actual standalone canonical checks
and two final source/evidence addenda before publication acceptance.
''')

# Recheck source author files after all copying; only the new worktree is edited.
for rel, expected in approved.items():
    assert sha((AUTHOR / rel).read_bytes()) == expected, rel
print(json.dumps({'project':str(PROJECT),'mathematical_files_unchanged':len(mathematical),
                  'files':sum(1 for p in PROJECT.rglob('*') if p.is_file()),
                  'transition_sha256':sha((PROJECT/'verification/packaging/TRANSITION.json').read_bytes())},indent=2))
