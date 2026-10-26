#!/usr/bin/env python3
"""Extend immutable support receipts with separately validated full-Target evidence.

This is a read-only integrity check, not another Lean or Linux execution.  The
historical support checker remains unchanged.  The latest Lean run's original
false aggregate is required to stay false; its raw-log terminal validation is
the separately identified acceptance basis.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, subprocess, sys

BASE = Path(__file__).resolve().parent
REPO = BASE.parents[5]
NEW = BASE.parent / 'independent-full-target-review'
artifacts = {}

def sha(p):
    assert p.is_file() and not p.is_symlink(), str(p)
    return hashlib.sha256(p.read_bytes()).hexdigest()

def bind(p, expected=None):
    actual = sha(p)
    if expected is not None:
        assert actual == expected, str(p)
    artifacts[str(p.relative_to(REPO))] = actual
    return actual

def read(p, expected=None):
    bind(p, expected)
    return json.loads(p.read_text())

def refs(value):
    if isinstance(value, dict):
        if set(value) >= {'path', 'sha256'}:
            path = Path(value['path'])
            assert not path.is_absolute() and '..' not in path.parts
            bind(REPO / path, value['sha256'])
        for child in value.values():
            refs(child)
    elif isinstance(value, list):
        for child in value:
            refs(child)

parser = argparse.ArgumentParser()
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
assert not args.output.exists(), 'Use a new output path; historical indexes are immutable.'

old_path = BASE / 'result-through-reverse-final.json'
old = read(old_path, '36d15fdd7511231825d62b17233096852a72d21e989490acf6255bc44b813037')
assert old['passed'] and old['approved_scopes'] == 35
assert old['distinct_current_project_Lean_sources'] == 161
assert not old['full_TR04_Target_proved'] and not old['authoritative_Linux_Comparator']
for path, digest in old['artifact_hashes'].items():
    bind(REPO / path, digest)

# Rerun the unchanged support checker, keeping its new timestamped output apart
# from the immutable historical result.  It has no mathematical/CI side effects.
old_checker = BASE / 'check-evidence-through-reverse-final.py'
bind(old_checker, old['checker_sha256'])
recheck_path = args.output.with_name(args.output.stem + '-historical-recheck.json')
assert not recheck_path.exists()
proc = subprocess.run([sys.executable, str(old_checker), '--output', str(recheck_path)],
                      cwd=REPO, capture_output=True, text=True)
assert proc.returncode == 0, proc.stdout + proc.stderr
recheck = read(recheck_path)
assert recheck['passed'] and recheck['approved_scopes'] == 35
assert recheck['current_project_source_hashes'] == old['current_project_source_hashes']
assert recheck['artifact_hashes'] == old['artifact_hashes']

config = read(NEW / 'source-lock.json', 'c355866f3541baa62b7bd5cea33a356fd5b907c52db7c9d828a1482e893b0383')
raw = read(NEW / 'run-attempt-1/result.json', 'e1eb538f8cd7ef0b2c60045be96b10266b670b3bbe7e916fdcee6baac18a3384')
terminal = read(NEW / 'TERMINAL_VALIDATION.json', '0994e225970bfaa2413d02b25ee953e53d1f644889102dcc87c76ffc36827c0e')
accepted = read(NEW / 'ACCEPTANCE.json', '716bf819e742b9b8d3e7060695e0a9330c4520f25e343c101da5ce416d016f1e')
assert raw['passed'] is False and terminal['passed'] and accepted['passed']
assert not terminal['retained_original_aggregate_passed']
assert not terminal['original_false_result_or_driver_rewritten']
assert not accepted['raw_result_relabelled_or_rewritten']
assert all(v['passed'] for v in raw['blocks'].values()) and len(raw['blocks']) == 7
assert raw['project_sources'] == 190 and len(raw['commands']) == 198
assert len(raw['declarations']) == 1821 and len(raw['private_or_local_named_declarations']) == 181
assert not raw['project_objects_reused'] and raw['pinned_external_dependency_objects_reused']
assert raw['package_input_sha256'] == config['package_inputs'] and len(config['package_inputs']) == 205
assert terminal['all7_positive_scopes_rechecked_from_raw_logs']
assert terminal['Challenge_target_exact_forbidden_sorryAx_rejected']
assert terminal['full_TR04_Target_proved'] and terminal['canonical_package_kernel_passed']
assert not terminal['comparison_target_accepted_as_proof'] and not terminal['authoritative_Linux_Comparator']
assert terminal['proof_commit'] == accepted['proof_commit'] == '027aaefbadf602ac460d0cf4cae7beed3181d712'
for path, digest in terminal['artifact_hashes'].items():
    bind(REPO / path, digest)
refs(accepted)
refs(terminal['retained_original_result'])

new_approvals = []
for rec in accepted['receipts']:
    approval = read(REPO / rec['path'], rec['sha256'])
    key = Path(rec['path']).stem.removeprefix('APPROVAL-')
    assert approval['passed'] and approval['reviewer'] == '/root/recover_verification'
    assert not approval['proof_source_authorship'] and not approval['proof_source_changes']
    assert not approval['retained_original_aggregate_passed']
    assert not approval['authoritative_Linux_Comparator']
    assert approval['full_TR04_Target_proved'] == (key in {'full_target', 'canonical_solution'})
    assert approval['canonical_package_kernel_passed'] == (key == 'canonical_solution')
    assert approval['result']['sha256'] == sha(NEW / 'TERMINAL_VALIDATION.json')
    assert approval['raw_execution_result']['sha256'] == sha(NEW / 'run-attempt-1/result.json')
    refs(approval)
    new_approvals.append(key)
assert sorted(new_approvals) == sorted(raw['blocks'])

for name, digest in config['package_inputs'].items():
    bind(REPO / config['canonical_project'] / name, digest)
    bind(NEW / 'run-attempt-1/sources' / name, digest)
for name, digest in raw['consumer_sha256'].items():
    bind(NEW / 'run-attempt-1/sources' / name, digest)
for cmd in raw['commands']:
    assert cmd['exit_code'] == cmd['expected_exit_code']
    bind(NEW / 'run-attempt-1' / cmd['log'], cmd['log_sha256'])
assert [(v['source'], v['exit_code']) for v in raw['commands'] if v['exit_code']] == [('Independent_Challenge_Negative.lean', 1)]

shared_union = dict(old['current_project_source_hashes'])
for source in config['shared_sources']:
    p = REPO / source['path']
    bind(p, source['sha256'])
    name = str(p.relative_to(REPO / 'lean-statements'))
    if name in shared_union:
        assert shared_union[name] == source['sha256']
    shared_union[name] = source['sha256']
canonical_lean = {k:v for k,v in config['package_inputs'].items() if k.endswith('.lean')}
assert len(canonical_lean) == 190 and len(shared_union) == 187
outside = {k:v for k,v in shared_union.items() if k not in canonical_lean}
assert len(outside) == 3
assert set(outside) == {'NLA/Proofs/TR04/TTMemoryLayoutMatrix.lean', 'NLA/Proofs/TR04/TTStrictOriginal.lean', 'NLA/Proofs/TR04/TensorCompressionLinear.lean'}
for name, digest in shared_union.items():
    assert sha(REPO / 'lean-statements' / name) == digest

# Preserve every ordinary verification source/log/diagnostic in the new audit.
# Compiled objects and interpreter bytecode are deliberately excluded.
for p in sorted(NEW.rglob('*')):
    if not p.is_file():
        continue
    relative_parts = p.relative_to(NEW).parts
    if any(x == '__pycache__' or x.startswith('objects') for x in relative_parts):
        continue
    assert p.suffix not in {'.olean', '.ilean', '.pyc'}, str(p)
    bind(p)
bind(Path(__file__))
out = {'passed': True, 'type': 'artifact_hash_integrity_only',
 'executed_utc': datetime.now(timezone.utc).isoformat(), 'checker_sha256': sha(Path(__file__)),
 'fresh_Lean_replayed_by_this_check': False, 'historical_support_index': {'path':str(old_path.relative_to(REPO)), 'sha256':sha(old_path)},
 'historical_support_checker_replayed': True, 'historical_support_scope_count':35,
 'new_scoped_approvals':new_approvals, 'approved_scopes':42,
 'shared_project_Lean_source_union':len(shared_union), 'current_shared_project_source_hashes':shared_union,
 'canonical_package_inputs':205, 'canonical_project_Lean_sources':190,
 'older_support_sources_outside_canonical_package':outside, 'distinct_relative_Lean_source_paths_across_canonical_and_support':193,
 'canonical_proof_commit':accepted['proof_commit'], 'full_Target_local_acceptance':{'path':str((NEW/'ACCEPTANCE.json').relative_to(REPO)), 'sha256':sha(NEW/'ACCEPTANCE.json')},
 'original_latest_aggregate_passed':False, 'separate_raw_terminal_validation_passed':True,
 'full_TR04_Target_proved':True, 'canonical_package_kernel_passed':True,
 'comparison_placeholder_accepted_as_proof':False, 'authoritative_Linux_Comparator':False,
 'proof_inputs_changed':False, 'artifact_hashes':artifacts,
 'scope_note':'Verifies retained historical support and separately accepted complete original Target/canonical local kernel evidence. The original false aggregate remains false; raw-log terminal validation supplies the explicit acceptance basis. No new Lean execution, actual Linux/Comparator acceptance or publication promotion is established by this checker.'}
args.output.write_text(json.dumps(out, indent=2)+'\n')
print(json.dumps({'passed':True, 'approved_scopes':42, 'shared_source_union':len(shared_union), 'canonical_Lean_sources':190, 'bound_artifacts':len(artifacts), 'sha256':sha(args.output)},indent=2))
