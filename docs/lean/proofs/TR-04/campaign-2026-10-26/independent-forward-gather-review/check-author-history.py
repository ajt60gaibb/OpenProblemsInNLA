#!/usr/bin/env python3
"""Read-only provenance for terminal author scopes and retained diagnostics."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
BASE=Path(__file__).resolve().parent;REPO=BASE.parents[5]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
artifacts={}
def bind(p,digest=None):
    assert p.is_file() and not p.is_symlink(),str(p)
    actual=sha(p)
    if digest is not None: assert actual==digest,str(p)
    artifacts[str(p.relative_to(REPO))]=actual
    return actual
c=json.loads((BASE/'source-lock.json').read_text())
specs={
 'candidate_gather':('candidate-gather-author/result.json','26822c70d1e4c8ff77d7eb33af64a30ce3e9e897db262d445c6d9fd335c15844','candidate-gather-author/sources'),
 'forward':('tt-forward-author/final/result.json','5ac2a2b08f5e1f174a658074f7b1a995ac6d33125e50ce9cc9c862de1fd798f0','tt-forward-author/final/sources')}
terminal=[]
for b in c['blocks']:
    location,digest,snapshot=specs[b['key']];p=BASE.parent/location
    bind(p,digest);d=json.loads(p.read_text())
    assert d.get('passed',d.get('success')) is True and d['project_objects_reused'] is False
    assert d['source_lock_sha256']==b['author_lock_sha256']
    bind(REPO/b['author_lock_path'],b['author_lock_sha256'])
    for r in b['records']:
        bind(BASE.parent/snapshot/r['path'].removeprefix('lean-statements/'),r['sha256'])
    for cmd in d.get('commands',[]):
        assert cmd['exit_code']==0;bind(Path(cmd['path']),cmd['sha256'])
    for e in d.get('evidence',[]): bind(p.parent/e['path'],e['sha256'])
    if b['key']=='candidate_gather':
        assert d['fresh_source_commands']==len(d['commands'])==110 and d['kernel_assertion_count']==32
    else:
        assert d['fresh_project_closure_source_count']==68 and d['fresh_kernel_command_count']==69
        assert d['authored_explicit_definitions_theorems_asserted']==76
        assert d['source_build_exit_code']==d['consumer_build_exit_code']==0
    assert all(set(x.strip() for x in entry.split(',')) <= {'propext','Classical.choice','Quot.sound'} for entry in d['printed_axiom_lists'])
    terminal.append({'key':b['key'],'result':str(p.relative_to(REPO)),'sha256':digest,'terminal_author_passed':True,'independent_acceptance':False})

old=BASE.parent/'tt-forward-author'
correction=json.loads((old/'consumer-correction.json').read_text())
bind(old/'consumer-correction.json')
assert correction['source_lock_sha256']==c['blocks'][1]['author_lock_sha256']
assert correction['development_consumer_old_exit']==1 and correction['development_consumer_new_exit']==0
assert correction['reuse_from_initial_or_development_objects'] is False
bind(old/'ExactConsumer.before-spacing-fix.lean',correction['old_consumer_sha256'])
bind(old/'ExactConsumer.lean',correction['new_consumer_sha256'])
assert not (old/'run/result.json').exists()
for n in ['consumer-development.log','consumer-development-2.log','driver.log','final-driver.log','run/source-build.log','replay.py','REPORT.md']:
    bind(old/n)
for rec in c['blocks'][1]['records']:
    bind(old/'run/sources'/rec['path'].removeprefix('lean-statements/'),rec['sha256'])
assert 'error:' in (old/'consumer-development.log').read_text()

control=json.loads((BASE/'private-auditor-preflight/result.json').read_text())
assert control['passed'] and control['driver_sha256']==sha(BASE/'replay.py')
assert control['positive_private_local_public_passed'] and control['custom_axiom_hidden_in_private_theorem_rejected']
assert not control['negative_control_accepted_as_a_proof']
bind(BASE/'private-auditor-preflight/result.json')
for cmd in control['commands']:
    assert cmd['exit_code']==cmd['expected_exit_code']
    bind(BASE/'private-auditor-preflight'/cmd['source'],cmd['source_sha256']);bind(REPO/cmd['log'],cmd['log_sha256'])
assert control['commands'][-1]['expected_exit_code']==1
out={'passed':True,'executed_utc':datetime.now(timezone.utc).isoformat(),'checker_sha256':sha(Path(__file__)),
 'scope':'Author terminal replays, retained forward syntax/interruption history and isolated independent auditor controls only.',
 'terminal_author_results':terminal,'forward_interrupted_run_accepted':False,'forward_interrupted_run_terminal_result_present':False,
 'forward_failed_development_consumer_accepted':False,'forward_final_fresh_replay_separate':True,
 'private_auditor_positive_negative_passed':True,'negative_fixture_accepted_as_proof':False,
 'artifact_hashes':artifacts,'proof_inputs_changed':False,'full_TR04_Target_proved':False,'authoritative_Linux_Comparator':False}
(BASE/'author-history.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':True,'artifact_count':len(artifacts),'sha256':sha(BASE/'author-history.json')},indent=2))
