#!/usr/bin/env python3
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib
BASE=Path(__file__).resolve().parent;REPO=BASE.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
p=BASE/'run-attempt-1/result.json';r=json.loads(p.read_text());lock=json.loads((BASE/'source-lock.json').read_text());block=lock['blocks'][0]
assert r['passed'] and len(r['commands'])==3 and all(c['exit_code']==0 for c in r['commands'])
assert r['driver_sha256']==sha(BASE/'replay.py')
assert r['lean_sha256']=='1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'
assert all(x['passed'] for k in ['dependencies_before','dependencies_after','original25_before','original25_after'] for x in r[k])
for record in block['records']:assert sha(REPO/record['path'])==record['sha256']
assert all(r['source_unchanged_after'].values()) and all(r['author_locks_unchanged_after'].values())
for c in r['commands']:assert sha(BASE/'run-attempt-1'/c['log'])==c['log_sha256']
approval={'passed':True,'approval':'APPROVED_FROZEN_SUPPORT_ONLY','reviewer':'/root/recover_verification','proof_source_authorship':[],'review_recorded_utc':datetime.now(timezone.utc).isoformat(),'execution_started_utc':r['started_utc'],'execution_finished_utc':r['finished_utc'],'scope':'MachineSVDMemory one frozen proof module and unchanged actual SVDMachine model, fresh two-source closure plus literal consumer.','source_review':'The literal matrixCell/readMatrix interface recovers actual row-major entries. U readback and outside-memory preservation follow actual writeSVD update priority without disjointness. Sigma and V readback use precisely the model OutputBlocksDisjoint hypotheses. No modified model, hidden readback assumption, or correctness oracle is introduced; empty dimensions are handled by their actual empty index types.','limits':'Memory-interface component only; no complete algorithm, full TR04 Target, termination, polynomial global cost, Linux, or Comparator acceptance claim.','author_source_lock':{'path':block['author_lock_path'],'sha256':block['author_lock_sha256']},'independent_source_lock_sha256':sha(BASE/'source-lock.json'),'result':{'path':str(p.relative_to(REPO)),'sha256':sha(p)},'scoped_kernel_result':r['blocks']['svd_memory'],'literal_consumer_bindings':r['consumer_bindings']['svd_memory'],'kernel_mode':'LeanCert kernel','axioms':r['blocks']['svd_memory']['observed_axioms'],'project_objects_reused':False,'ten_exact_clean_pins_before_after':True,'original25_byte_exact_against_2b_before_after':True,'private_or_local_explicit_declarations':[],'prior_consumer_diagnostic':{'path':str((BASE/'prior-diagnostic.json').relative_to(REPO)),'sha256':sha(BASE/'prior-diagnostic.json'),'retained_honestly':True,'proof_sources_changed':False},'full_TR04_Target_proved':False,'authoritative_Linux_Comparator':False}
q=BASE/'APPROVAL.json';q.write_text(json.dumps(approval,indent=2)+'\n');print(json.dumps({'path':str(q.relative_to(REPO)),'sha256':sha(q),'result_sha256':sha(p),'passed':True},indent=2))
