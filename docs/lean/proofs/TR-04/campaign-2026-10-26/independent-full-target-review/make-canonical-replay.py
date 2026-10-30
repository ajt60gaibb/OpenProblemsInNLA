#!/usr/bin/env python3
"""Derive the canonical driver without weakening the named proof auditor."""
from pathlib import Path
import hashlib,json
B=Path(__file__).resolve().parent
prior=B/'replay-shared-precanonical.py'
s=prior.read_text()
def replace(old,new):
    global s
    assert s.count(old)==1,old[:100]
    s=s.replace(old,new)
replace("PROJECT=REPO/'lean-statements'","PROJECT=REPO/'tensor-computations/TR-04/lean'")
replace("for r in config['union']:assert sha((REPO/r['path']).read_bytes())==r['sha256'],r['path']",'''assert sha((REPO/config['canonical_freeze']['path']).read_bytes())==config['canonical_freeze']['sha256']
def package_state():
 actual={}
 for p in PROJECT.rglob('*'):
  rel=p.relative_to(PROJECT)
  if '.lake' in rel.parts:continue
  assert not p.is_symlink(),('Canonical input symlink',str(rel))
  if p.is_file():actual[str(rel)]=sha(p.read_bytes())
 assert actual==config['package_inputs'],'Frozen205 ordinary input set differs'
 return actual
package_before=package_state()
for r in config['union']:assert sha((PROJECT/r['path'].removeprefix('lean-statements/')).read_bytes())==r['sha256'],r['path']
for r in config['shared_sources']:
 assert sha((REPO/r['path']).read_bytes())==r['sha256']==sha((PROJECT/r['path'].removeprefix('lean-statements/')).read_bytes())
author_receipts=json.loads((BASE/'author-terminal-receipts.json').read_text())
assert author_receipts['passed'] and len(author_receipts['terminal_author_results'])==6
for n,h in author_receipts['artifact_hashes'].items():assert sha((REPO/n).read_bytes())==h
package_data={n:(PROJECT/n).read_bytes() for n in config['package_inputs']}''')
replace(" assert not re.search(r'\\b(sorry|admit|axiom|implemented_by|unsafe)\\b|trustCompiler|debug\\.skipKernelTC',lexical),('Trust construct',name)",''' if name=='FullChallenge.lean':
  specification='theorem target : NLA.Statements.TR04.Target := by\\n  sorry'
  assert lexical.count(specification)==1 and len(re.findall(r'\\bsorry\\b',lexical))==1
  lexical=lexical.replace(specification,'theorem target : NLA.Statements.TR04.Target := by comparisonPlaceholder')
 assert not re.search(r'\\b(sorry|admit|axiom|implemented_by|unsafe)\\b|trustCompiler|debug\\.skipKernelTC',lexical),('Trust construct',name)''')
replace("for b in config['blocks']:\n for m in b['roots']:freeze(m)","for b in config['blocks']:\n for m in b['roots']:freeze(m)\nfreeze('FullChallenge')")
replace("all_declarations=[d for n,data in frozen.items() for d in declarations_of(n,data)]", "all_declarations=[d for n,data in frozen.items() if n not in config['canonical_comparison_sources'] for d in declarations_of(n,data)]")
replace(" declaration=match[1];prefix=name.removesuffix('.'+declaration);assert prefix!=name", " declaration=match[1];prefix=None if name==declaration else name.removesuffix('.'+declaration);assert prefix!=name")
replace(" code=f'namespace {prefix}\\n'+'\\n'.join(source_opens)+f'\\nexample{header} := by\\n  exact @{name} '+ ' '.join(args)+f'\\nend {prefix}\\n'", " code=(f'namespace {prefix}\\n' if prefix else 'section\\n')+'\\n'.join(source_opens)+f'\\nexample{header} := by\\n  exact @{name} '+ ' '.join(args)+(f'\\nend {prefix}\\n' if prefix else '\\nend\\n')")
anchor="parser=argparse.ArgumentParser();parser.add_argument('--run-dir',default='run-attempt-1');args=parser.parse_args()"
replace(anchor,'''comparison_declarations=declarations_of('Challenge.lean',frozen['Challenge.lean'])
assert all(d['visibility']=='public' for d in comparison_declarations)
negative='import FullChallenge\\n'+preamble
for d in comparison_declarations:
 kind='theorem' if d['kind'] in {'theorem','lemma'} else 'inductive' if d['kind'] in {'inductive','structure'} else 'definition'
 negative+=f'#audit_named {json.dumps(d["name"])} "Challenge" "public" {json.dumps(kind)}\\n'
negative+='#print axioms NLA.TR04.target\\n#audit_named "NLA.TR04.target" "FullChallenge" "public" "theorem"\\n'
negative_name='Independent_Challenge_Negative.lean';consumers[negative_name]=negative.encode()
parser=argparse.ArgumentParser();parser.add_argument('--run-dir',default='run-attempt-1');args=parser.parse_args()''')
old="for name,data in {**frozen,**consumers}.items():"
assert s.count(old)==2
s=s.replace(old,"for name,data in {**package_data,**consumers}.items():")
replace("  assert len(build_order)==len(frozen)+len(consumers) and len(set(build_order))==len(frozen)+len(consumers)", "  build_order.extend(n for n in frozen if n not in build_order)\n  build_order.append(negative_name)\n  assert len(build_order)==len(frozen)+len(consumers) and len(set(build_order))==len(frozen)+len(consumers)")
replace("   command.update(source=name,log=logfile,log_sha256=sha(log.encode()))", "   command.update(source=name,log=logfile,log_sha256=sha(log.encode()),expected_exit_code=1 if name==negative_name else 0,comparison_specification=name=='FullChallenge.lean')")
replace("   if command['exit_code']:break", "   if command['exit_code']!=command['expected_exit_code']:break")
replace("result['dependencies_after']=dependencies();result['original25_after']=originals()", "result['dependencies_after']=dependencies();result['original25_after']=originals()\nresult['package_input_sha256']=package_before\nresult['package_inputs_unchanged_after']=package_state()==package_before\nresult['shared_original_sources_unchanged_after']={r['path']:sha((REPO/r['path']).read_bytes())==r['sha256'] for r in config['shared_sources']}\nresult['author_terminal_receipts_sha256']=sha((BASE/'author-terminal-receipts.json').read_bytes())")
replace("result['passed']=all(b['passed'] for b in result['blocks'].values()) and len(result['commands'])==len(frozen)+len(consumers) and all(c['exit_code']==0 for c in result['commands'])",'''neg=commands.get(negative_name);neglog=(EVIDENCE/neg['log']).read_text() if neg else ''
legacy_expected=[d['name'] for d in comparison_declarations]
legacy_axioms=re.findall(r'AUDITED_AXIOMS (\\S+) \\[([^\\]]*)\\]',neglog)
legacy_kinds=re.findall(r'AUDITED_KIND (\\S+) (\\S+)',neglog)
negative_passed=bool(neg and neg['exit_code']==1 and
 sorted(n for n,_ in legacy_axioms)==sorted(legacy_expected) and
 sorted(n for n,_ in legacy_kinds)==sorted(legacy_expected+['NLA.TR04.target']) and
 all(set(a.strip() for a in body.split(',') if a.strip())<=ALLOWED for _,body in legacy_axioms) and
 'depends on sorry or unrecognized axioms' in neglog and 'sorryAx' in neglog)
result['challenge_negative_control']={'passed':negative_passed,'expected_exit_code':1,'actual_exit_code':neg['exit_code'] if neg else None,
 'source':negative_name,'original_legacy_named_checks':len(legacy_expected),'original_legacy_declarations':comparison_declarations,
 'comparison_target_accepted_as_proof':False,'specification_module':'FullChallenge','proof_module':'FullSolution'}
result['passed']=all(b['passed'] for b in result['blocks'].values()) and len(result['commands'])==len(frozen)+len(consumers) and all(c['exit_code']==c['expected_exit_code'] for c in result['commands']) and negative_passed and result['package_inputs_unchanged_after'] and all(result['shared_original_sources_unchanged_after'].values())''')
replace("result['mathematical_kernel_acceptance_only']=True", "result['mathematical_kernel_acceptance_only']=True\nresult['canonical_package_kernel_passed']=result['passed']\nresult['authoritative_Linux_Comparator']=False")
(B/'replay.py').write_text(s)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(B/'canonical-driver-provenance.json').write_text(json.dumps({'prior_driver_sha256':sha(prior),'driver_sha256':sha(B/'replay.py'),
 'changes':['Use exact frozen205-file canonical package as source, with all184 shared copies hash-identical to the reviewed originals.',
 'Compile the two comparison-context modules separately; accept only the exact single FullChallenge Target placeholder as a specification and require its proof-trust rejection.',
 'Audit188 proof-source inventories, including retained Solution exports and new proof/identity wrappers. Keep legacy Challenge constants in their separate imported environment.',
 'Support global original theorem names in the same complete raw-header parser; all kind/kernel/transitive-axiom/private-identity/lexical/pin/original guards remain.',
 'Require six terminal author receipts, complete ordinary-input snapshot, unchanged package/shared sources and expected negative-control failure.'],
 'kernel_auditor_preamble_changed':False,'proof_source_changes':False},indent=2)+'\n')
print(sha(B/'replay.py'))
