#!/usr/bin/env python3
"""Read-only terminal author evidence and independent auditor controls."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
BASE=Path(__file__).resolve().parent;REPO=BASE.parents[5]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
artifacts={}
def bind(p,digest=None):
    assert p.is_file() and not p.is_symlink(),str(p)
    actual=sha(p)
    if digest is not None:assert actual==digest,str(p)
    artifacts[str(p.relative_to(REPO))]=actual
    return actual
c=json.loads((BASE/'source-lock.json').read_text())
specs={
 'final_callers':('final-caller-author/result.json','a8665d15f67b62998dfa44eecc8556b17675556e53e561ca48c10ec1c46e98b9',78,39),
 'copy349':('final-copy349-author/result.json','eb79818409f23850eb5bdb49f0d56809d136d24456f9887a4b5bc27cdd481b79',79,8),
 'reverse':('tt-reverse-author/final/result.json','11109b7ac6ccab21189c1751d1309bf393b93c214fc7db2d7b8d91b7a2e5f80b',85,123),
 'child_svd_loop':('tt-child-svd-loop-author/result.json','2a4484a4de1d280d44f9906fe0b8e1cdeeb6fe91f1790b63a4850f6ba2b3742a',87,20)}
terminal=[]
for b in c['blocks']:
    location,digest,commands,names=specs[b['key']];p=BASE.parent/location
    bind(p,digest);d=json.loads(p.read_text())
    assert d.get('passed',d.get('success')) is True and d['project_objects_reused'] is False
    assert d['source_lock_sha256']==b['author_lock_sha256']
    bind(REPO/b['author_lock_path'],b['author_lock_sha256'])
    for r in b['records']:
        bind(p.parent/'sources'/r['path'].removeprefix('lean-statements/'),r['sha256'])
    for cmd in d.get('commands',[]):
        assert cmd['exit_code']==0;bind(Path(cmd['path']),cmd['sha256'])
    for e in d.get('evidence',[]):bind(p.parent/e['path'],e['sha256'])
    for name,digest2 in d.get('logs',{}).items():bind(p.parent/name,digest2)
    if b['key'] in {'final_callers','copy349'}:
        assert d['fresh_source_commands']==len(d['commands'])==commands and d['kernel_assertion_count']==names
        inputs=json.loads((p.parent/'replay-input-lock.json').read_text())
        bind(p.parent/'replay-input-lock.json')
        assert inputs['source_lock_sha256']==b['author_lock_sha256'] and inputs['project_object_reuse'] is False
        assert inputs['fresh_source_count']==len(b['records']) and inputs['expected_commands']==commands
        assert inputs['kernel_assertion_count']==names
        bind(p.parent/'run-author.py',inputs['driver_sha256'])
        bind(p.parent/'ExactConsumer.lean',inputs['consumer_sha256'])
        assert inputs['compiler_sha256']=='1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'
        bind(p.parent/'REPORT.md')
    elif b['key']=='reverse':
        assert d['fresh_project_closure_source_count']==84 and d['fresh_kernel_command_count']==commands
        assert d['authored_explicit_definitions_theorems_asserted']==names
        assert d['source_build_exit_code']==d['consumer_build_exit_code']==0
    else:
        assert d['project_modules_rebuilt']==86 and d['successful_commands']==commands
        assert d['public_declaration_kernel_checks']==names and d['verbatim_public_theorem_headers']==16
        assert d['reviewed_original_inputs_unchanged']==25 and d['only_standard_three_axioms']
        bind(BASE.parent/'replay-child-svd-loop.py',d['replay_driver_sha256'])
        bind(p.parent/'ConsumerInput.lean.txt',d['consumer_input_sha256'])
        bind(p.parent/'TTChildSVDLoopConsumerWithTrust.lean.txt',d['consumer_sha256'])
        authorlock=json.loads((REPO/b['author_lock_path']).read_text())
        bind(REPO/authorlock['consumer_input']['path'],authorlock['consumer_input']['sha256'])
    for entry in d.get('printed_axiom_lists',[]):
        assert set(x.strip() for x in entry.split(','))<={'propext','Classical.choice','Quot.sound'}
    terminal.append({'key':b['key'],'result':str(p.relative_to(REPO)),'sha256':sha(p),
        'terminal_author_passed':True,'fresh_commands':commands,'author_named_assertions':names,
        'independent_acceptance':False})

# Retain the real development-only reverse consumer error and its correction.
old=BASE.parent/'tt-reverse-author'
for name in ['ExactConsumer.before-update-type-fix.lean','ExactConsumer.lean',
             'consumer-development.log','consumer-development-2.log','final-driver.log','replay.py','REPORT.md']:
    bind(old/name)
assert 'error:' in (old/'consumer-development.log').read_text()
assert 'error:' not in (old/'consumer-development-2.log').read_text()
assert (old/'ExactConsumer.before-update-type-fix.lean').read_bytes()!=(old/'ExactConsumer.lean').read_bytes()
assert (old/'ExactConsumer.lean').read_bytes()==(old/'final/sources/ExactConsumer.lean').read_bytes()

control=json.loads((BASE/'private-identity-controls/result.json').read_text())
assert control['passed'] and control['driver_sha256']==sha(BASE/'replay.py')
assert control['two_modules_with_same_private_source_name_checked_distinctly']
assert control['private_local_public_kinds_passed'] and control['hidden_custom_axiom_in_exact_second_module_rejected']
assert control['wrong_module_rejected'] and control['wrong_actual_kind_rejected']
assert not control['negative_control_accepted_as_proof']
bind(BASE/'private-identity-controls/result.json')
for cmd in control['commands']:
    assert cmd['exit_code']==cmd['expected_exit_code']
    bind(BASE/'private-identity-controls'/cmd['source'],cmd['source_sha256']);bind(REPO/cmd['log'],cmd['log_sha256'])
assert sum(cmd['expected_exit_code']==1 for cmd in control['commands'])==3
out={'passed':True,'executed_utc':datetime.now(timezone.utc).isoformat(),'checker_sha256':sha(Path(__file__)),
 'scope':'Terminal author replays, retained reverse development-consumer diagnostic, and independent exact-private-identity positive/negative controls only.',
 'terminal_author_results':terminal,'reverse_failed_development_consumer_accepted':False,
 'reverse_terminal_fresh_run_separate':True,'private_identity_positive_and_three_negative_controls_passed':True,
 'negative_fixture_accepted_as_proof':False,'artifact_hashes':artifacts,
 'proof_inputs_changed':False,'full_TR04_Target_proved':False,'authoritative_Linux_Comparator':False}
(BASE/'author-history.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':True,'artifact_count':len(artifacts),'sha256':sha(BASE/'author-history.json')},indent=2))
