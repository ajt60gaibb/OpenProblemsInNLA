#!/usr/bin/env python3
"""Read-only authentication/search audit; writes only this review directory."""
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
PACKET = Path('/private/tmp/nla-lean-next-20260915/next-statements/MI27-feasibility-20260918-referee2')
MI24 = Path('/private/tmp/nla-lean-next-20260915/MI24-canonical-package-local332')
MI13 = Path('/private/tmp/nla-lean-next-20260915/MI13-canonical-package-local53')
MATHLIB = Path('/private/tmp/nla-lean-local-shared-20260916/.lake/packages/mathlib')
REPO = Path('/Users/georgestepaniants/Research/OpenProblemsInNLA')
EXPECTED = '3ae88bd593f88f2872e5318bc712aa2637a48ffa384c80470aba2b2ec8e57ab3'

def bind(path):
    data = path.read_bytes()
    return {'path': str(path), 'sha256': sha256(data).hexdigest(), 'bytes': len(data)}

manifest_record = bind(PACKET / 'MANIFEST.json')
assert manifest_record['sha256'] == EXPECTED
packet_manifest = json.loads((PACKET / 'MANIFEST.json').read_text())
packet_checks = {}
for name, expected in packet_manifest['files'].items():
    record = bind(PACKET / name)
    record['expected_sha256'] = expected
    assert record['sha256'] == expected, name
    packet_checks[name] = record

reuse_spec = json.loads((PACKET / 'REUSE-CANDIDATES.json').read_text())
reuse_checks = {}
for name, spec in reuse_spec['files'].items():
    record = bind(Path(spec['source']))
    assert record['sha256'] == spec['sha256'], name
    reuse_checks[name] = record
closure = set()
def visit(module):
    if module in closure:
        return
    closure.add(module)
    path = MI24 / (module.replace('.', '/') + '.lean')
    for line in path.read_text().splitlines():
        match = re.match(r'^import\s+(NLA\.[A-Za-z0-9_.]+)\s*$', line)
        if match:
            visit(match.group(1))
for root in reuse_spec['roots']:
    visit(root)
assert len(closure) == 7
assert {module.replace('.', '/') + '.lean' for module in closure} == set(reuse_checks)

acceptance = bind(Path(reuse_spec['local_acceptance_record']))
assert acceptance['sha256'] == reuse_spec['acceptance_record_sha256']
primary_checks = {}
for name, spec in reuse_spec['primary_files'].items():
    record = bind(Path(spec['path']))
    assert record['sha256'] == spec['sha256'], name
    primary_checks[name] = record
for name in [
    'Analysis/Matrix/HermitianFunctionalCalculus.lean',
    'Analysis/Matrix/Order.lean',
    'LinearAlgebra/Matrix/PosDef.lean',
    'LinearAlgebra/QuadraticForm/Signature.lean',
]:
    primary_checks[name] = bind(MATHLIB / 'Mathlib' / name)

mi13_manifest = json.loads((MI13 / 'PACKAGE-MANIFEST.json').read_text())
guidance = {}
for name in ['REVIEWING.md', 'rubrics/correctness.md', 'rubrics/generality.md',
             'rubrics/proof-quality.md', 'rubrics/reuse.md', 'rubrics/attribution.md']:
    rel = 'sources/standards/TauCetiProject/TauCetiReview/' + name
    record = bind(MI13 / rel)
    assert record['sha256'] == mi13_manifest['files'][rel], rel
    guidance[name] = record

searches = [
    ('entropy', ['rg', '-n', 'trace.*log|log.*trace|trace.*deriv|deriv.*trace|hasFDerivAt.*cfc|HasFDerivAt.*cfc|Frenkel|Hirche|quantumEntropy|vonNeumannEntropy', 'Mathlib']),
    ('inertia', ['rg', '-n', 'inertia|negative.*(eigen|index)|PosDef.*congr|posDef.*congr|signature.*Hermitian|Sylvester', 'Mathlib/LinearAlgebra', 'Mathlib/Analysis/Matrix']),
    ('absolute-continuity', ['rg', '-n', 'integral_deriv_eq_sub|LipschitzOnWith.absolutelyContinuousOnInterval', 'Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean', 'Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean']),
    ('spectral-cfc', ['rg', '-n', 'lemma cfc_eq|spectrum_real_eq_range_eigenvalues|protected noncomputable def cfc', 'Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean']),
]
search_records = []
for label, command in searches:
    run = subprocess.run(command, cwd=MATHLIB, text=True, capture_output=True, check=False)
    assert run.returncode in (0, 1), (label, run.stderr)
    output = HERE / (label + '.log')
    output.write_text(run.stdout + run.stderr)
    search_records.append({'label': label, 'cwd': str(MATHLIB), 'command_argv': command,
                           'exit_code': run.returncode, 'log': bind(output)})

audit = {
    'created_at_utc': datetime.now(timezone.utc).isoformat(),
    'reviewer': '/root/mi27_route_referee1',
    'scope': 'Independent mathematical/prose contract and route review; no Lean or checker execution',
    'packet_manifest': manifest_record,
    'packet_files_authenticated': packet_checks,
    'repo_sources': {name: bind(REPO / name) for name in ['AGENTS.md', 'problem_ids.json', 'matrix-inequalities-and-norms/MI-27/README.md', 'matrix-inequalities-and-norms/MI-27/problem.tex']},
    'reuse_files_authenticated': reuse_checks,
    'local_reuse_roots': reuse_spec['roots'],
    'local_reuse_closure': sorted(closure),
    'reuse_acceptance_record_read_not_rerun': acceptance,
    'mathlib_revision_from_packet_pin': reuse_spec['mathlib_revision_from_pin'],
    'primary_source_files': primary_checks,
    'guidance_source_package_manifest': bind(MI13 / 'PACKAGE-MANIFEST.json'),
    'pinned_guidance': guidance,
    'static_searches': search_records,
    'web_reads': [
        {'url': 'https://arxiv.org/html/2208.12194v4', 'sections': 'Sections 2-4; matrix-pencil Lemmas 1-5 and Theorem 6', 'tool': 'web.run open/find; successful returned content', 'local_html_snapshot': None},
        {'url': 'https://arxiv.org/html/2306.12343v3#S2.SS3', 'sections': 'Hockey-stick definitions on normalized states; Theorem 2.2; Corollary 2.3, equations (2.22)-(2.27)', 'tool': 'web.run open/find; successful returned content', 'local_html_snapshot': None},
    ],
    'not_executed': ['Lean compiler', 'LeanCert', 'Comparator', 'kernel export', 'sandbox check', 'Tau Ceti review runner', 'numerical experiment', 'fresh upstream/fork/PR enumeration', 'Git mutation', 'push', 'PR submission', 'external message'],
    'approval': {
        'mathematical_prose_contracts_C01_C20_and_N01_N03': 'approve',
        'full_original_target_correspondence': 'approve',
        'route_architecture': 'mathematically coherent; substantial C11 and C16 internal proof obligations remain',
        'supplemental_route_notes': 'reviewer derivations; separate helper review required if adopted',
        'Lean_statement_elaboration': 'not run',
        'proof_implementation_authorization_by_this_review_alone': False,
        'proof_completion': False,
        'whole_problem_verification': False,
        'new_mathematical_resolution_count_change': 0,
        'complete_Lean_verification_count_change': 0,
    },
}
(HERE / 'AUDIT.json').write_text(json.dumps(audit, indent=2) + '\n')
review_files = {path.name: bind(path)['sha256'] for path in sorted(HERE.iterdir())
                if path.is_file() and path.name != 'MANIFEST.json'}
result = {'sealed_at_utc': datetime.now(timezone.utc).isoformat(),
          'reviewer': '/root/mi27_route_referee1',
          'reviewed_packet_manifest_sha256': EXPECTED,
          'verdict': 'APPROVE mathematical prose contracts and full-target correspondence only',
          'no_Lean_or_Comparator_execution': True,
          'source_audit': 'AUDIT.json', 'files': review_files}
(HERE / 'MANIFEST.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'packet_file_hashes_pass': len(packet_checks), 'reuse_closure_modules': len(closure),
                  'primary_files_bound': len(primary_checks), 'guidance_hashes_pass': len(guidance),
                  'review_manifest': bind(HERE / 'MANIFEST.json')}, indent=2))
