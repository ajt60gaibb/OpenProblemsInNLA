#!/usr/bin/env python3
"""Derive a distinct promotion auditor without editing the candidate auditor."""
from pathlib import Path
import ast,hashlib,json
B=Path(__file__).resolve().parent;REPO=B.parents[5]
old=B.parent/'independent-linux-candidate-algebra/audit-linux.py'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(old)=='82303ba91fbe0584d6ed4fb25890510fa31a13cb511330de5d69663b7cfabba2'
s=old.read_text()
replacements=[
 ('original TR04 candidate','original TR04 promoted'),
 ("HEAD='027aaefbadf602ac460d0cf4cae7beed3181d712'","HEAD='09cd782576559502787fb536bc1427bf64b7b3e4'"),
 ('RUN=40405628070','RUN=40408919808'),
 ("FREEZE=DOC+'CANONICAL_PACKAGE_PREACCEPTANCE_FREEZE_2026-10-26.json'","FREEZE=DOC+'CANONICAL_PROMOTION_FREEZE_2026-10-26.json'"),
 ("FREEZE_SHA='8ee1d4585f3c0a60b101ec962fa9631ebbc043270cf35360669b8018152301eb'","FREEZE_SHA='44b5df77ea7ed70c35aac6e87b2001f2b6860a36f58f1156a50d01a3c83374f7'"),
 ("'exact-prior205-package-freeze-and-own-approval'","'exact-final205-promotion-freeze-and-prior-canonical-approval'"),
 ("reviewer='/root/recover_algebra'","reviewer='/root/recover_verification'"),
 ("scope='Independent read-only integrity audit of actual original GitHub Linux/Comparator bytes; own authored mathematical prerequisites excluded from independent mathematical source scope'","scope='Independent non-author read-only integrity audit of actual original final-promotion GitHub Linux/Comparator bytes; complete mathematical source acceptance is separately bound'"),
 ("'Semantic proof fidelity and my authored prerequisites rely on separately bound independent source/kernel reviews; receipt integrity review does not claim independent authorship of those proofs.'","'Complete semantic proof fidelity is established in my separately bound non-author source/kernel acceptance. This artifact auditor performs no new Lean execution.'")]
for a,b in replacements:
    assert s.count(a)==1,(a,s.count(a));s=s.replace(a,b)
start=s.index("  original_manifest=decode(blob(HEAD,freeze['original_archive']['path']))")
end=s.index("  check('all217-permanent-ID-path-pairs'",start)
old_preservation=s[start:end]
assert old_preservation.count("check('all25-live-archived-originals:'")==1
new_preservation='''  original_path=freeze['preserved_original_archive'];original_manifest=decode(blob(HEAD,original_path))
  check('exact25-original-archive-manifest',sha(blob(HEAD,original_path))=='81d4086ffcbc92eb2b1c92f815ed1d859f2393d0b47d2fca0c3275968d308047' and len(original_manifest['records'])==25)
  candidate='027aaefbadf602ac460d0cf4cae7beed3181d712'
  oldfreeze=decode(blob(candidate,DOC+'CANONICAL_PACKAGE_PREACCEPTANCE_FREEZE_2026-10-26.json'))
  check('promotion-only-formalization205-input-delta',set(oldfreeze['inputs'])==set(inputs) and [q for q in inputs if inputs[q]!=oldfreeze['inputs'][q]]==['formalization.yaml'] and inputs['formalization.yaml']=='1302638065dbc0a3ea98b0b0730811b1b8828ddb95ac06441e400bcb11249633')
  proposal=decode(blob(HEAD,freeze['proposal']['path']))
  check('exact-prior-approved-promotion-v2',sha(blob(HEAD,freeze['proposal']['path']))==freeze['proposal']['sha256']=='c352fedca0c34cf23c89e41fdc82cb870ff552b5d50c6fe01a1fc6b5d47a11b0' and proposal['revision']==2 and proposal['post_promotion_package_inputs']==inputs)
  approval_path=DOC+'independent-promotion-review/APPROVAL.json';promotion_approval=decode(blob(HEAD,approval_path))
  check('own-exact-nonauthor-promotion-source-approval',sha(blob(HEAD,approval_path))=='8c17dfa96dea9c4e6c36b196678bc59de9073d622bd9edbee6fa7c544a9e66c8' and promotion_approval['passed'] and promotion_approval['proposal_sha256']==freeze['proposal']['sha256'] and not promotion_approval['proposed_final_metadata_Linux_verified'])
  replacements={x['destination']:x for x in proposal['proposed_replacements']}
  check('exact-two-approved-descriptive-replacements',set(replacements)=={PROJECT+'/formalization.yaml','tensor-computations/TR-04/README.md'})
  for q,x in replacements.items():
   check('actual-approved-promotion-bytes:'+q,sha(blob(HEAD,q))==x['proposed_sha256'] and blob(HEAD,q)==blob(HEAD,x['proposed_path'])==blob(merge,q)==(repo/q).read_bytes())
  for q in sorted(q for q in inputs if q.endswith('.lean')):
   check('all190-final-Lean-identical-proof-candidate:'+q,blob(HEAD,PROJECT+'/'+q)==blob(candidate,PROJECT+'/'+q))
  for c in original_manifest['records']:
   original=blob(candidate,c['original_path']);live=blob(HEAD,c['original_path']);archived=blob(HEAD,c['archive_path'])
   changed=c['original_path']=='tensor-computations/TR-04/README.md'
   check('all25-live-archived-originals:'+c['original_path'],sha(original)==c['sha256'] and archived==original==blob(merge,c['archive_path']) and live==blob(merge,c['original_path'])==(repo/c['original_path']).read_bytes() and (live==blob(HEAD,replacements[c['original_path']]['proposed_path']) if changed else live==original))
  original=blob(candidate,'tensor-computations/TR-04/README.md');promoted=blob(HEAD,'tensor-computations/TR-04/README.md');marker=b'## Problem statement\\n'
  check('entire-original-problem-statement-suffix-byte-exact',original.count(marker)==promoted.count(marker)==1 and original.split(marker,1)[1]==promoted.split(marker,1)[1])
  for name in ['Challenge.lean','Solution.lean','SPEC.md','README.md']:
   check('legacy-canonical-original-byte-exact:'+name,blob(HEAD,PROJECT+'/'+name)==blob(candidate,PROJECT+'/'+name))
  registry=decode(blob(HEAD,'problem_ids.json'))
  check('all217-ID-registry-exact-original-proof-head',len(registry)==217 and blob(HEAD,'problem_ids.json')==blob(candidate,'problem_ids.json'))
  for ident,q in registry.items():
   if ident!='TR-04':check('all216-other-original-problem-pages:'+ident,blob(HEAD,q)==blob(candidate,q)==blob(merge,q)==(repo/q).read_bytes())
  acceptance_path=DOC+'independent-full-target-review/ACCEPTANCE.json';acceptance=decode(blob(HEAD,acceptance_path))
  check('complete-nonauthor-mathematical-source-acceptance',sha(blob(HEAD,acceptance_path))=='716bf819e742b9b8d3e7060695e0a9330c4520f25e343c101da5ce416d016f1e' and acceptance['passed'] and acceptance['full_TR04_Target_proved'] and not acceptance['proof_source_authorship'] and not acceptance['retained_original_aggregate_passed'])
'''
s=s[:start]+new_preservation+s[end:]
old_ast=ast.parse(old.read_text());new_ast=ast.parse(s)
old_funcs={n.name:ast.dump(n,include_attributes=False) for n in old_ast.body if isinstance(n,ast.FunctionDef)}
new_funcs={n.name:ast.dump(n,include_attributes=False) for n in new_ast.body if isinstance(n,ast.FunctionDef)}
assert set(old_funcs)==set(new_funcs)
assert [k for k in old_funcs if old_funcs[k]!=new_funcs[k]]==['main']
# Every actual checker, kernel/axiom/control/isolation/build/log guard outside
# promotion source identity and original preservation remains text exact.
for part in ["  challenge=blob(merge,PROJECT+'/Challenge.lean')", "  tool=result['tool_receipt']"]:
    assert s[s.index(part):].split(' report=dict(',1)[0]==old.read_text()[old.read_text().index(part):].split(' report=dict(',1)[0]
q=B/'audit-linux.py';assert not q.exists();q.write_text(s)
report={'passed':True,'scope':'Auditor preparation only; no final run/artifact acceptance',
 'candidate_reference_sha256':sha(old),'final_auditor_sha256':sha(q),
 'fixed_head':'09cd782576559502787fb536bc1427bf64b7b3e4','fixed_run':40408919808,
 'fixed_promotion_freeze_sha256':'44b5df77ea7ed70c35aac6e87b2001f2b6860a36f58f1156a50d01a3c83374f7',
 'all_non_main_function_ASTs_identical':True,
 'all_proof_kind_axiom_kernel_comparator_control_isolation_dependency_tool_and_raw_log_guards_text_identical':True,
 'preservation_delta':'All25 original archived bytes remain exact;24 live originals exact; only TR04 display README equals separately approved proposalv2. All190 Lean inputs and216 other pages additionally compared against original proof commit027.',
 'source_only_promotion_approval_bound':'8c17dfa96dea9c4e6c36b196678bc59de9073d622bd9edbee6fa7c544a9e66c8',
 'final_CI_accepted':False,'candidate_auditor_or_receipt_modified':False}
(B/'PREPARATION.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
