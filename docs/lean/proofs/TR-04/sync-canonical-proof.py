#!/usr/bin/env python3
"""Copy/check the full concrete TR04 closure while retaining the legacy scaffold.

This establishes byte identity only; independent and Linux acceptance are separate.
"""
import argparse,hashlib,json,re,shutil
from pathlib import Path
REPO=Path(__file__).resolve().parents[4]
SOURCE=REPO/'lean-statements'
PROJECT=REPO/'tensor-computations/TR-04/lean'
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--write',action='store_true')
args=parser.parse_args()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
entries=['NLA.Proofs.TR04.MachineTTFull','NLA.Proofs.TR04.MachineTTRecursiveChild','Reviewed.TR04']
exports=['Challenge.lean','Solution.lean','Check.lean','FullChallenge.lean','FullSolution.lean',
 'Identity.lean','comparator.json','lakefile.toml','lake-manifest.json','lean-toolchain']
for name in exports:
 assert (PROJECT/name).is_file(),name
originals=json.loads((REPO/'docs/lean/proofs/TR-04/campaign-2026-10-23/input-lock.json').read_text())['records']
legacy=[]
for rec in originals:
 if rec['path'] in ['tensor-computations/TR-04/lean/Challenge.lean','tensor-computations/TR-04/lean/Solution.lean']:
  assert sha(REPO/rec['path'])==rec['sha256'],rec['path']
  legacy.append(rec)
assert len(legacy)==2
visited=set();active=set();ordered=[]
def visit(module):
 if module in visited:return
 assert module not in active,module
 active.add(module)
 relative=Path(module.replace('.','/')+'.lean');src=SOURCE/relative
 assert src.is_file(),module
 imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',src.read_text(),re.M)
 for child in imports:
  if child.startswith(('NLA.','Reviewed.')):visit(child)
 active.remove(module);visited.add(module);ordered.append((module,relative,src,imports))
for entry in entries:visit(entry)
copies=[]
for module,relative,src,imports in ordered:
 dst=PROJECT/relative
 if args.write:
  dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
 assert dst.is_file() and src.read_bytes()==dst.read_bytes(),relative
 copies.append({'module':module,'source':str(src.relative_to(REPO)),'destination':str(dst.relative_to(REPO)),
  'source_sha256':sha(src),'destination_sha256':sha(dst),'imports':imports})
expected_lean={str(relative) for _,relative,_,_ in ordered}|{p for p in exports if p.endswith('.lean')}
actual_lean={str(p.relative_to(PROJECT)) for p in PROJECT.rglob('*.lean') if '.lake' not in p.relative_to(PROJECT).parts}
assert actual_lean==expected_lean,{'extra':sorted(actual_lean-expected_lean),'missing':sorted(expected_lean-actual_lean)}
config=json.loads((PROJECT/'comparator.json').read_text())
assert config['challenge_module']=='FullChallenge' and config['solution_module']=='FullSolution'
assert config['theorem_names']==['candidate_count_le_first_mode','cyclic_window_count_le_first_mode','NLA.TR04.target']
assert config['definition_names']==[] and set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
lock={'entries':entries,'literal_target':'NLA.TR04.target : NLA.Statements.TR04.Target',
 'fixed_program':'NLA.Proofs.TR04.ttProgram','fixed_C':1000000,'fixed_k':5,
 'legacy_scaffold_note':'Original Challenge/Solution remain byte exact at their old paths; tr04Statement over arbitrary unfoldingRank is retained and is not asserted proved. FullChallenge/FullSolution compare the independently reviewed concrete computational Target.',
 'retained_original_lean_files':legacy,'actual_copied_source_count':len(copies),
 'actual_proof_source_count':sum(c['module'].startswith('NLA.Proofs.TR04.') for c in copies),
 'actual_canonical_Lean_input_count':len(expected_lean),'copies':copies,'selected_exports':config['theorem_names'],
 'package_exports':{name:sha(PROJECT/name) for name in exports},
 'scope':'Exact proof/model/boundary/config copies and retained legacy exports; fresh kernel, independent fidelity and Linux/Comparator evidence are separate.'}
p=PROJECT/'proof-source-lock.json'
if args.write:p.write_text(json.dumps(lock,indent=2)+'\n')
else:assert p.is_file() and json.loads(p.read_text())==lock,'Source lock mismatch'
print(json.dumps({'passed':True,'mode':'write' if args.write else 'check','copies':len(copies),
 'proofs':lock['actual_proof_source_count'],'Lean_inputs':len(expected_lean),'selected_exports':len(config['theorem_names'])}))
