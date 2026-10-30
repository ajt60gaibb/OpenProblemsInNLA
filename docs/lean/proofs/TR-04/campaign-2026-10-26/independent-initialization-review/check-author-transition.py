#!/usr/bin/env python3
"""Read-only binding of failed/successful author runs, source identity and controls."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess

BASE = Path(__file__).resolve().parent
REPO = BASE.parents[5]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
artifacts = {}
def bind(p, digest=None):
    assert p.is_file() and not p.is_symlink(), str(p)
    actual = sha(p)
    if digest is not None: assert actual == digest, str(p)
    artifacts[str(p.relative_to(REPO))] = actual
    return actual

old = BASE.parent / 'tt-initialization-author'
new = BASE.parent / 'tt-initialization-author-attempt-2'
oldhash = 'cb4ddf637e0d2171944c45cea80e3b6617085d14d3d6824b1eba0bd830c06b7b'
newhash = 'de6012d95f102d1eb406c8fe8332db4e34329e3ffe416fbae598ec25db118d7b'
a = json.loads((old/'source-lock.json').read_text())
b = json.loads((new/'source-lock.json').read_text())
bind(old/'source-lock.json',oldhash); bind(new/'source-lock.json',newhash)
changed = [k for k in a.keys() | b.keys() if a.get(k) != b.get(k)]
assert changed == ['execution_started_utc'], changed
assert len(a['project_closure']) == len(b['project_closure']) == 71
assert len(a['authored_modules']) == 6 and len(a['authored_declarations']) == 55
for rec in a['project_closure']:
    bind(REPO/rec['path'],rec['sha256'])
    for root in [old,new]: bind(root/'sources'/rec['path'].removeprefix('lean-statements/'),rec['sha256'])
for rec in a['reviewed_original_inputs']: bind(REPO/rec['path'],rec['sha256'])
assert len(a['reviewed_original_inputs']) == 25
failed = json.loads((old/'ATTEMPT_FAILED.json').read_text())
bind(old/'ATTEMPT_FAILED.json')
assert failed['passed'] is False and failed['consumer_exit_code'] == 1
assert failed['all_source_commands_succeeded'] and failed['project_source_count'] == 71
assert failed['source_lock_sha256'] == oldhash
for p, digest in failed['artifacts'].items(): bind(REPO/p,digest)
assert 'error:' in (old/'consumer.log').read_text()

result = json.loads((new/'result.json').read_text())
bind(new/'result.json','2948c812c02c08f3c5e66b0f0df499ab62d401d5ef62dc3ca1df9174f192fd7d')
assert result['passed'] and result['source_lock_sha256'] == newhash
assert result['project_modules_rebuilt'] == 71 and result['successful_commands'] == 72
assert result['public_declaration_kernel_checks'] == result['axiom_reports_checked'] == 55
assert result['verbatim_public_theorem_headers'] == 39 and result['literal_consumer_examples'] == 41
assert result['project_objects_reused'] is False and result['only_standard_three_axioms']
assert len(result['pinned_dependencies']) == 10 and all(x['clean'] for x in result['pinned_dependencies'])
for name,digest in result['logs'].items(): bind(new/name,digest)
bind(new/'TTInitializationConsumerWithTrust.lean.txt',result['consumer_sha256'])
for p in ['prepare-original-cb4.py','source-lock-original-cb4.json','replay-original-cb4.py','private-name-provenance-original-cb4.json']:
    bind(BASE/p)
before = json.loads((BASE/'source-lock-original-cb4.json').read_text())
after = json.loads((BASE/'source-lock.json').read_text())
assert before['union'] == after['union']
assert before['private_name_map'] == after['private_name_map']
for key in ['records','owned','declarations','owned_declarations','author_selected_public_declarations','roots','literal_endpoints']:
    assert before['blocks'][0][key] == after['blocks'][0][key],key
assert before['blocks'][0]['author_lock_sha256'] == oldhash
assert after['blocks'][0]['author_lock_sha256'] == newhash

generator = BASE.parent/'generate-initialization-consumer.py'
check = subprocess.run(['python3',str(generator),'--check'],cwd=REPO,text=True,capture_output=True)
assert check.returncode == 0,check.stderr
bind(generator);bind(BASE.parent/'TTInitializationConsumer.lean.txt');bind(BASE.parent/'replay-tt-initialization.py')
fixture = BASE/'private-auditor-preflight-2'
control = json.loads((fixture/'result.json').read_text())
assert control['passed'] and control['driver_sha256'] == sha(BASE/'replay.py')
assert control['positive_private_local_public_passed'] and control['custom_axiom_hidden_in_private_theorem_rejected']
assert not control['negative_control_accepted_as_a_proof']
for directory in ['private-auditor-preflight','private-auditor-preflight-2']:
    for p in sorted((BASE/directory).iterdir()):
        if p.is_file(): bind(p)
for c in control['commands']:
    bind(fixture/c['source'],c['source_sha256']);bind(REPO/c['log'],c['log_sha256'])
    assert c['exit_code'] == c['expected_exit_code']
assert control['commands'][-1]['expected_exit_code'] == 1
out = {'passed': True,'recorded_utc':datetime.now(timezone.utc).isoformat(),
    'scope':'Author run transition and independent auditor controls; not an independent Lean acceptance receipt.',
    'author_source_lock_difference': changed,'all_71_source_records_and_55_selected_names_identical':True,
    'old_author_attempt_accepted':False,'old_failure_reason':failed['reason'],
    'new_author_terminal_result':str((new/'result.json').relative_to(REPO)),
    'new_author_result_sha256':sha(new/'result.json'),
    'author_generator_read_only_check':{'argv':check.args,'exit_code':check.returncode,'stdout':check.stdout,'stderr':check.stderr},
    'independent_private_auditor_positive_negative_passed':True,'negative_fixture_accepted_as_proof':False,
    'artifact_hashes':artifacts,'checker_sha256':sha(Path(__file__)),
    'proof_source_changes':False,'full_TR04_Target_proved':False,'authoritative_Linux_Comparator':False}
(BASE/'author-transition-and-controls.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':True,'artifact_count':len(artifacts),'sha256':sha(BASE/'author-transition-and-controls.json')},indent=2))
