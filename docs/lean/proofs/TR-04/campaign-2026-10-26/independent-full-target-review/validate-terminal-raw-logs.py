#!/usr/bin/env python3
"""Correct only terminal aggregation; never rerun or relabel the retained run."""
from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,re
B=Path(__file__).resolve().parent;REPO=B.parents[5];R=B/'run-attempt-1'
ALLOWED={'propext','Classical.choice','Quot.sound'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
artifacts={}
def bind(p,h=None):
    assert p.is_file() and not p.is_symlink(),str(p)
    actual=sha(p)
    if h is not None:assert actual==h,str(p)
    artifacts[str(p.relative_to(REPO))]=actual
    return actual
r=json.loads((R/'result.json').read_text());c=json.loads((B/'source-lock.json').read_text())
bind(R/'result.json');bind(B/'source-lock.json',r['source_lock_sha256'])
bind(B/'replay-attempt-1.py',r['driver_sha256']);bind(B/'source_inventory.py',r['inventory_sha256'])
assert r['passed'] is False and 'exception' not in r
assert r['challenge_negative_control']['passed'] is False
assert all(v['passed'] for v in r['blocks'].values()) and len(r['blocks'])==7
assert r['project_sources']==190 and len(r['commands'])==198 and len(r['declarations'])==1821
assert r['project_objects_reused'] is False and r['pinned_external_dependency_objects_reused'] is True
assert r['lean_sha256']=='1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'
for k in ['dependencies_before','dependencies_after']:assert len(r[k])==10 and all(v['passed'] for v in r[k])
for k in ['original25_before','original25_after']:assert len(r[k])==25 and all(v['passed'] for v in r[k])
assert r['package_inputs_unchanged_after'] and all(r['source_unchanged_after'].values())
assert all(r['shared_original_sources_unchanged_after'].values()) and all(r['author_locks_unchanged_after'].values())
assert r['package_input_sha256']==c['package_inputs'] and len(c['package_inputs'])==205
for n,h in c['package_inputs'].items():bind(R/'sources'/n,h);bind(REPO/c['canonical_project']/n,h)
for x in c['shared_sources']:bind(REPO/x['path'],x['sha256'])
for n,h in r['consumer_sha256'].items():bind(R/'sources'/n,h)
commands={x['source']:x for x in r['commands']};negative='Independent_Challenge_Negative.lean'
assert [(x['source'],x['exit_code']) for x in r['commands'] if x['exit_code']]==[(negative,1)]
for x in r['commands']:
    assert x['exit_code']==x['expected_exit_code'];bind(R/x['log'],x['log_sha256'])
    assert x['argv'][0].endswith('/lean-4.33.1-darwin_aarch64/bin/lean')
proof_instance_theorems={'NLA.Proofs.TR04.'+n for n in ['squaredErrorProgram_nonzero_realRegisters','thresholdScanProgram_nonzero_reals',
 'bestCandidateProgram_nonzero_realRegisters','ttStartup_nonzero_realRegisters','ttMetadata_nonzero_realRegisters','ttFirstSelection_nonzero_reals','ttInitScalar_nonzero_reals']}
scopes=[]
for b in c['blocks']:
    info=r['consumer_bindings'][b['key']];cmd=commands[info['source']];assert cmd['exit_code']==0
    log=(R/cmd['log']).read_text()
    kinds=re.findall(r'AUDITED_KIND (\S+) (\S+)',log)
    axioms=re.findall(r'AUDITED_AXIOMS (\S+) \[([^\]]*)\]',log)
    actual=re.findall(r'AUDITED_ACTUAL (\S+) (\S+) (\S+)',log)
    expected=[(d['audit_id'],'theorem' if d['kind'] in {'theorem','lemma'} or d['name'] in proof_instance_theorems else 'inductive' if d['kind'] in {'structure','inductive'} else 'definition') for d in b['declarations']]
    assert sorted(kinds)==sorted(expected)
    assert sorted(n for n,_ in axioms)==sorted(d['audit_id'] for d in b['declarations'])
    assert sorted(actual)==sorted((d['name'],d['audit_id'],d['visibility']) for d in b['declarations'])
    assert all(set(a.strip() for a in xs.split(',') if a.strip())<=ALLOWED for _,xs in axioms)
    assert sorted({a.strip() for _,xs in axioms for a in xs.split(',') if a.strip()})==sorted(ALLOWED)
    scopes.append({'key':b['key'],'passed':True,'named_exact_kind_kernel_and_axiom_checks':len(expected),'complete_raw_public_headers':len(info['literal_examples'])})
negcmd=commands[negative];log=(R/negcmd['log']).read_text()
legacy=r['challenge_negative_control']['original_legacy_declarations'];assert len(legacy)==9
kinds=re.findall(r'AUDITED_KIND (\S+) (\S+)',log)
axioms=re.findall(r'AUDITED_AXIOMS (\S+) \[([^\]]*)\]',log)
actual=re.findall(r'AUDITED_ACTUAL (\S+) (\S+) (\S+)',log)
legacy_kinds=[(d['name'],'theorem' if d['kind']=='theorem' else 'inductive' if d['kind']=='structure' else 'definition') for d in legacy]
assert sorted(kinds)==sorted(legacy_kinds+[('NLA.TR04.target','theorem')])
assert sorted(actual)==sorted((n,n,'public') for n,_ in legacy_kinds+[('NLA.TR04.target','theorem')])
assert sorted(n for n,_ in axioms)==sorted([d['name'] for d in legacy]+['NLA.TR04.target'])
for n,xs in axioms:
    observed={a.strip() for a in xs.split(',') if a.strip()}
    if n=='NLA.TR04.target':assert observed==(ALLOWED|{'sorryAx'})
    else:assert observed<=ALLOWED
assert log.count('error:')==1
assert "error: #assert_trust: 'NLA.TR04.target' depends on sorry or unrecognized axioms" in log
assert 'sorryAx: sorryAx' in log and negcmd['exit_code']==1
for name in ['canonical-input-review.json','author-terminal-receipts.json','raw-literal-header-check.json','production-harness-proof-commit-binding.json']:
    d=json.loads((B/name).read_text());assert d['passed'];bind(B/name)
    for p,h in d.get('artifact_hashes',{}).items():bind(REPO/p,h)
assert json.loads((B/'production-harness-proof-commit-binding.json').read_text())['input_sha256']==c['package_inputs']
out={'passed':True,'recorded_utc':datetime.now(timezone.utc).isoformat(),'checker_sha256':sha(Path(__file__)),
 'type':'independent_exact_raw_log_terminal_validation','retained_original_aggregate_passed':False,
 'retained_original_result':{'path':str((R/'result.json').relative_to(REPO)),'sha256':sha(R/'result.json')},
 'retained_original_driver_sha256':r['driver_sha256'],'original_false_result_or_driver_rewritten':False,
 'cause':'The original negative-control parser expected no axiom record after elabCommand reports an error. Lean continues after the correctly rejected trust assertion and emits the explicit target sorryAx record.',
 'correction':'Require all9 legacy records to have permitted axioms, and the exact Target record to have exactly standard3+sorryAx, together with the unique exact expected trust error and exit1. No proof, consumer, source, input or Lean execution is changed.',
 'fresh_Lean_commands_previously_executed':198,'successful_source_build_and_positive_consumer_commands':197,
 'expected_negative_rejections':1,'new_Lean_commands_executed_by_this_validation':0,
 'canonical_inputs':205,'canonical_Lean_sources':190,'proof_context_sources':188,'comparison_context_sources':2,
 'proof_environment_named_identities':1821,'scopes':scopes,'proof_commit':'027aaefbadf602ac460d0cf4cae7beed3181d712',
 'all7_positive_scopes_rechecked_from_raw_logs':True,'Challenge_target_exact_forbidden_sorryAx_rejected':True,
 'comparison_target_accepted_as_proof':False,'full_TR04_Target_proved':True,'canonical_package_kernel_passed':True,
 'authoritative_Linux_Comparator':False,'proof_source_changes':False,'artifact_hashes':artifacts}
(B/'TERMINAL_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':True,'sha256':sha(B/'TERMINAL_VALIDATION.json'),'bound_artifacts':len(artifacts)}))
