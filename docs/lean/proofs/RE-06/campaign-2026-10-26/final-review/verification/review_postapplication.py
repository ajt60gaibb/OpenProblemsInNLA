#!/usr/bin/env python3
"""Read-only immutable postapplication/catalog audit; no proof or CI execution."""
import argparse,collections,copy,hashlib,io,json,re,subprocess,tarfile
from pathlib import Path
REF='669f3cd681b22882836d081a04652880ce39ba24'
CANDIDATE='0c6d346763a932eb2d379f555e66d8ab3dbf3255'
PREFIX='randomized-and-low-rank-approximation/RE-06/lean/'
DOC='docs/lean/proofs/RE-06/'
PAGE='randomized-and-low-rank-approximation/RE-06/README.md'
def sha(b):return hashlib.sha256(b).hexdigest()
def main():
 p=argparse.ArgumentParser()
 for n in ['repo','packet','output']:p.add_argument('--'+n,type=Path,required=True)
 a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True);checks=[]
 def git(*x):return subprocess.check_output(['git','-C',str(a.repo),*x])
 def blob(n,r=REF):return git('show',r+':'+n)
 def ck(n,v,**kw):
  checks.append({'check':n,'pass':bool(v),**kw})
  if not v:raise RuntimeError('Failed check: '+n)
 def snapshot(r,paths,prefix=''):
  raw=git('archive',r,*paths)
  with tarfile.open(fileobj=io.BytesIO(raw)) as tf:return {e.name[len(prefix):]:tf.extractfile(e).read() for e in tf if e.isfile()}
 parent=git('rev-parse',REF+'^').decode().strip();packetraw=(a.packet/'PROMOTION_PACKET.json').read_bytes();packet=json.loads(packetraw)
 ck('exact_approved_v2_packet',sha(packetraw)=='5712b7add2bb2fca11062bd6f83b482a74b6c087579b270505e0492cac5db845')
 expected=set(['CATALOG.md','README.md',DOC+'CANDIDATE_README.md',DOC+'LINUX_CI_RECEIPT.md',DOC+'ORIGINAL.md',DOC+'README.md',DOC+'campaign-2026-10-26/PROMOTION_APPLICATION.json',*[DOC+'campaign-2026-10-26/promotion-checks/'+f'{i:02}.log' for i in range(1,8)],DOC+'campaign-2026-10-26/promotion-checks/RESULT.json','docs/lean/statements/COVERAGE.md','docs/lean/statements/inventory.json',PAGE,PREFIX+'PACKAGE_LOCK.json',PREFIX+'README.md',PREFIX+'formalization.yaml','randomized-and-low-rank-approximation/README.md'])
 changed=set(git('diff-tree','--no-commit-id','--name-only','-r',REF).decode().splitlines());ck('exact22_applied_archive_display_check_files',len(changed)==22 and changed==expected)
 application=json.loads(blob(DOC+'campaign-2026-10-26/PROMOTION_APPLICATION.json'));ck('application_record_parent_packet_and_unsealed_final_gate',application['preceding_commit']==parent and application['packet_sha256']==sha(packetraw) and application['new_lock_sha256']==packet['proposed_lock_sha256'] and not application['final_Linux_accepted'] and not application['proof_or_executable_changes'])
 paths={'formalization.yaml':PREFIX+'formalization.yaml','PACKAGE_LOCK.json':PREFIX+'PACKAGE_LOCK.json','lean-README.md':PREFIX+'README.md','canonical-README.md':PAGE,'ORIGINAL.md':DOC+'ORIGINAL.md','CANDIDATE_README.md':DOC+'CANDIDATE_README.md','proof-README.md':DOC+'README.md'}
 for name,target in paths.items():
  b=(a.packet/name).read_bytes();e=packet['files'][name];ck('exact_applied_approved_file:'+target,blob(target)==b and sha(b)==e['sha256'] and len(b)==e['bytes'] and application['applied_files'][target]==e)
 for n,digest in application['approved_input_hashes'].items():ck('retained_exact_scope_approval:'+n,sha(blob(n))==digest)
 now=snapshot(REF,[PREFIX],PREFIX);before=snapshot(parent,[PREFIX],PREFIX);candidate=snapshot(CANDIDATE,[PREFIX],PREFIX)
 ck('same295_package_file_set',len(now)==295 and set(now)==set(before)==set(candidate));ck('only3_descriptive_canonical_inputs_differ',sorted(n for n in now if now[n]!=before[n])==['PACKAGE_LOCK.json','README.md','formalization.yaml'] and before==candidate)
 lock=json.loads(now['PACKAGE_LOCK.json']);ck('exact_promoted_lock',sha(now['PACKAGE_LOCK.json'])=='e712ded5fbc472ab9fa999de9a1fa885aa86b0b88276f2a55afbc01a7a7a921a' and len(lock['files'])==294 and set(lock['files'])==set(now)-{'PACKAGE_LOCK.json'})
 for n,e in lock['files'].items():ck('current_locked_input:'+n,sha(now[n])==e['sha256'] and len(now[n])==e['bytes'])
 runtime=[n for n in now if n.endswith('.lean') and not n.startswith('reviews/')];ck('91_runtime_inputs',len(runtime)==91)
 for n in runtime:ck('unchanged_runtime:'+n,now[n]==before[n]==candidate[n])
 mapping=json.loads(now['SOURCE_MAP.json']);ck('278_copy_bindings_unchanged',mapping==json.loads(candidate['SOURCE_MAP.json']) and len(mapping['copies'])==278)
 for e in mapping['copies']:ck('unchanged_upstream_copy:'+e['path'],now[e['path']]==candidate[e['path']] and sha(now[e['path']])==e['sha256'] and len(now[e['path']])==e['bytes'])
 idsraw=blob('problem_ids.json');ids=json.loads(idsraw);ck('all217_IDs_paths_unchanged',len(ids)==217 and idsraw==blob('problem_ids.json',parent)==blob('problem_ids.json',CANDIDATE))
 allpages=snapshot(REF,list(ids.values()));oldpages=snapshot(parent,list(ids.values()));counts=collections.Counter()
 for identity,path in ids.items():
  m=re.search(rb'^\*\*Status:\*\*\s*(.+?)\s*$',allpages[path],re.M);ck('canonical_retained_ID_page:'+identity,m is not None and (path==PAGE or allpages[path]==oldpages[path]));counts[m[1].decode()]+=1
 ck('independent217_page_status_counts',dict(counts)=={'Lean verified':88,'Partially resolved':62,'Open':36,'Solved':30,'Solution claimed':1},counts=dict(counts))
 ck('exact_originals_and_context_suffix',blob(DOC+'ORIGINAL.md')==blob(PAGE,parent)==blob(PAGE,CANDIDATE) and blob(DOC+'CANDIDATE_README.md')==candidate['README.md'] and blob(PAGE).split(b'## Context and notation',1)[1]==blob(PAGE,parent).split(b'## Context and notation',1)[1])
 summary_old=b'**Resolution evidence:** 31 solved (published or independently audited); 87 solved with Lean verification.';summary_new=b'**Resolution evidence:** 30 solved (published or independently audited); 88 solved with Lean verification.'
 ck('root_display_only_derived_count_delta',blob('README.md')==blob('README.md',parent).replace(summary_old,summary_new))
 for path in ['CATALOG.md','randomized-and-low-rank-approximation/README.md']:
  old=blob(path,parent);new=blob(path);oldrow=next(x for x in old.splitlines() if b'| [RE-06]' in x);expected_bytes=old.replace(oldrow,oldrow.replace('**✅ SOLVED**'.encode(),'**🏆 LEAN VERIFIED**'.encode()))
  if path=='CATALOG.md':expected_bytes=expected_bytes.replace(summary_old,summary_new)
  ck('only_RE06_badge_and_derived_counts:'+path,new==expected_bytes)
 oldcov=blob('docs/lean/statements/COVERAGE.md',parent);oldrow=next(x for x in oldcov.splitlines() if b'| [RE-06]' in x);ck('coverage_only_RE06_status_delta',blob('docs/lean/statements/COVERAGE.md')==oldcov.replace(oldrow,oldrow.replace(b'| Solved |',b'| Lean verified |')))
 oi=json.loads(blob('docs/lean/statements/inventory.json',parent));ni=json.loads(blob('docs/lean/statements/inventory.json'));expected_inventory=copy.deepcopy(oi);row=next(e for e in expected_inventory['entries'] if e['id']=='RE-06');row['status']='Lean verified';row['canonical_sha256']=sha(blob(PAGE));row['canonical_unchanged_from_base']=False;row['statement_complexity_estimate']['domains'].append('finite-algebra-or-combinatorics');ck('inventory_exact_expected_RE06_status_hash_and_keyword_triage',ni==expected_inventory)
 cr=json.loads(blob(DOC+'campaign-2026-10-26/promotion-checks/RESULT.json'));ck('seven_retained_author_commands_correct_scope',cr['passed'] and cr['expected_commands']==7 and len(cr['records'])==7)
 for e in cr['records']:
  b=blob(DOC+'campaign-2026-10-26/promotion-checks/'+e['log']);ck('retained_author_check_log:'+e['log'],e['exit_code']==0 and sha(b)==e['sha256'])
 ck('retained17_ID_tests_and45_statement_boundaries',b'Ran 17 tests' in blob(DOC+'campaign-2026-10-26/promotion-checks/03.log') and b'PASS: 45 statement metadata records; no mathematical proof claim' in blob(DOC+'campaign-2026-10-26/promotion-checks/06.log'))
 receipt=blob(DOC+'LINUX_CI_RECEIPT.md');ck('candidate_receipt_does_not_claim_final_run',b'A fresh actual Linux run bound to those promoted inputs is still required before the final evidence seal' in receipt and b'40415515989' in receipt and b'1322d6c23e833cba4223b466a3717af1a197b904' in receipt and b'c8750e229b3795d6fd681fe6a25dad2db285c90c8570011b8c6c7954a5674e1e' in receipt)
 for n,d in [(DOC+'campaign-2026-10-26/linux-candidate-v2-author/collection/run-40415515989/terminal/original-artifact.zip','44cc441ef976ff1da8ee765920cc62c1dbffd96eaa0bc6cc410f784c70179eff'),(DOC+'campaign-2026-10-26/linux-candidate-v2-author/collection/run-40415515989/terminal/job-121897153349.log','5fd6c119cb9342e3f10c506281e26b27649b7d796b736b59588ba98f9f47ebd8')]:ck('receipt_linked_original_byte_binding:'+n,sha(blob(n))==d)
 r={'pass':all(e['pass'] for e in checks),'reviewer':'/root/verification','non_author':True,'scope':'Postapplication display/catalog/originals only; final Linux approval pending separately','source_commit':REF,'parent_commit':parent,'candidate_commit':CANDIDATE,'promotion_packet_sha256':sha(packetraw),'checks':checks,'counts':dict(counts),'new_Lean_execution':False,'new_Linux_execution':False,'script_sha256':sha(Path(__file__).read_bytes())};(a.output/'RESULT.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'pass':r['pass'],'checks':len(checks),'counts':dict(counts)},indent=2))
if __name__=='__main__':main()
