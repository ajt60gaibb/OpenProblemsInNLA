#!/usr/bin/env python3
"""Bind all six terminal author runs, without claiming independent acceptance."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
B=Path(__file__).resolve().parent;REPO=B.parents[5]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
artifacts={}
def bind(p,h=None):
    assert p.is_file() and not p.is_symlink(),str(p)
    actual=sha(p)
    if h is not None:assert actual==h,str(p)
    artifacts[str(p.relative_to(REPO))]=actual
specs={
 'first_context':('tt-first-loop-context-author/result.json','653abf4680965263272a7dcba57c7e8a9b0dc0f1be88fb87b8f96b5d39d63417',149,150,15),
 'minimum_strict':('minimum-strict-author/result.json','fadfe303c6e0e746e94f67f8c247e5a6aeaccbdc3efac3a956b617bcb1f6469d',107,108,13),
 'store_context':('store-context-author/result.json','71e53d99ac23e62a512e0781b957ac04b7f4fe24f96e27111e7529d8f61074c2',160,161,6),
 'recursive_execution':('tt-recursive-execution-author/final/result.json','d2ca58e2b98c911c26e33b08943294d92ce9d408e23e8159b166f7adc9e09e61',107,108,43),
 'final_context':('final-context-author/result.json','2cbce765d8314fe3256b50ccda445749c52b8f632a9feb0624febec54aec5ec5',164,165,2),
 'full_target':('tt-full-target-author/result.json','c56f71100bede99e907d00e3c9da3f3c2cd9e08ff766315a839b439a5994b180',182,183,14)}
config=json.loads((B/'source-lock.json').read_text());out=[]
for block in config['blocks']:
    if block['key']=='canonical_solution':continue
    rel,h,sources,commands,names=specs[block['key']];p=B.parent/rel;bind(p,h);d=json.loads(p.read_text())
    assert d.get('passed',d.get('success')) is True and d['project_objects_reused'] is False
    assert d['source_lock_sha256']==block['author_lock_sha256'];bind(REPO/block['author_lock_path'],block['author_lock_sha256'])
    extras={r['path'] for r in block['reviewer_extra_sources']}
    records=[r for r in block['records'] if r['path'] not in extras];assert len(records)==sources==block['author_record_count']
    for r in records:bind(p.parent/'sources'/r['path'].removeprefix('lean-statements/'),r['sha256'])
    for c in d.get('commands',[]):
        assert c['exit_code']==0;bind(Path(c['path']),c['sha256'])
    for e in d.get('evidence',[]):bind(p.parent/e['path'],e['sha256'])
    for name,digest in d.get('logs',{}).items():bind(p.parent/name,digest)
    if 'successful_commands' in d:
        assert d['project_modules_rebuilt']==sources and d['successful_commands']==commands
        assert d['public_declaration_kernel_checks']==names and d['only_standard_three_axioms']
        assert d['reviewed_original_inputs_unchanged']==25
        candidates=[q for q in B.parent.glob('*.py') if sha(q)==d['replay_driver_sha256']]
        assert len(candidates)==1;bind(candidates[0],d['replay_driver_sha256'])
        bind(p.parent/'ConsumerInput.lean.txt',d['consumer_input_sha256'])
    elif 'fresh_source_commands' in d:
        assert d['fresh_source_commands']==commands==len(d['commands']) and d['kernel_assertion_count']==names
        inputs=json.loads((p.parent/'replay-input-lock.json').read_text());bind(p.parent/'replay-input-lock.json')
        assert inputs['source_lock_sha256']==block['author_lock_sha256']
        bind(p.parent/'run-author.py',inputs['driver_sha256']);bind(p.parent/'ExactConsumer.lean',inputs['consumer_sha256'])
        assert inputs['compiler_sha256']=='1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'
    else:
        assert d['fresh_project_closure_source_count']==sources and d['fresh_kernel_command_count']==commands
        assert d['source_build_exit_code']==d['consumer_build_exit_code']==0
        assert d['authored_explicit_definitions_theorems_asserted']==names
        bind(p.parent.parent/'replay.py',d['driver_sha256'])
    for xs in d.get('printed_axiom_lists',[]):assert set(v.strip() for v in xs.split(','))<={'propext','Classical.choice','Quot.sound'}
    out.append({'key':block['key'],'result':str(p.relative_to(REPO)),'sha256':h,
        'terminal_author_passed':True,'sources':sources,'successful_commands':commands,'consumer_kernel_assertions':names,
        'independent_acceptance':False})
assert len(out)==6
data={'passed':True,'executed_utc':datetime.now(timezone.utc).isoformat(),'checker_sha256':sha(Path(__file__)),
 'scope':'Six distinct frozen terminal author replays only; no independent/source/canonical/Linux/Comparator acceptance is inferred.',
 'terminal_author_results':out,'artifact_hashes':artifacts,'proof_source_changes':False,'independent_acceptance':False}
(B/'author-terminal-receipts.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({'passed':True,'artifacts':len(artifacts),'sha256':sha(B/'author-terminal-receipts.json')}))
