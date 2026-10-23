#!/usr/bin/env python3
"""Check/copy the exact TR06 source closure and all retained published sources.

This establishes source identity, not mathematical fidelity or Linux acceptance.
"""
import argparse,hashlib,json,re,shutil
from pathlib import Path
REPO=Path(__file__).resolve().parents[4]
SOURCE=REPO/'lean-statements'
PROJECT=REPO/'tensor-computations/TR-06/lean'
ENTRY='NLA.Proofs.TR06.RetainedBoundaryMean'
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--write',action='store_true')
args=parser.parse_args()
def sha(data):return hashlib.sha256(data).hexdigest()
exports=['Challenge.lean','Identity.lean','Solution.lean','Reviewed/TR06.lean',
 'comparator.json','lakefile.toml','lake-manifest.json','lean-toolchain','ORIGINAL.md','LICENSE']
for name in exports:
 if not (PROJECT/name).is_file():raise RuntimeError('Missing reviewed export/build input: '+name)
visited=set();visiting=set();ordered=[]
def visit(module):
 if module in visited:return
 if module in visiting:raise RuntimeError('Import cycle: '+module)
 relative=Path(module.replace('.','/')+'.lean');src=SOURCE/relative
 if not src.is_file():raise RuntimeError('Missing source: '+str(src))
 visiting.add(module)
 imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',src.read_text(),re.M)
 for child in imports:
  if child.startswith(('NLA.','Reviewed.')):visit(child)
 visiting.remove(module);visited.add(module);ordered.append((module,relative,src,imports))
visit(ENTRY)
retained=json.loads((REPO/'docs/lean/proofs/TR-06/campaign-2026-10-18/retained-58-source-lock.json').read_text())
retained_records=retained['records']
if len(retained_records)!=58:raise RuntimeError('Expected all 58 retained published sources')
for item in retained_records:
 src=REPO/item['campaign_path']
 if sha(src.read_bytes())!=item['sha256']:raise RuntimeError('Retained source changed: '+str(src))
 visit(str(src.relative_to(SOURCE).with_suffix('')).replace('/','.'))
copies=[]
for module,relative,src,imports in ordered:
 dest=PROJECT/relative
 if args.write:
  dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest)
 if not dest.is_file() or src.read_bytes()!=dest.read_bytes():raise RuntimeError('Canonical copy differs: '+str(relative))
 copies.append({'module':module,'source':str(src.relative_to(REPO)),
  'destination':str(dest.relative_to(REPO)),'source_sha256':sha(src.read_bytes()),
  'destination_sha256':sha(dest.read_bytes()),'imports':imports})
expected_lean={str(relative) for _,relative,_,_ in ordered}|{'Challenge.lean','Identity.lean','Solution.lean','Reviewed/TR06.lean'}
actual_lean={str(p.relative_to(PROJECT)) for p in PROJECT.rglob('*.lean') if '.lake' not in p.relative_to(PROJECT).parts}
if actual_lean!=expected_lean:raise RuntimeError('Unexpected canonical Lean source set')
config=json.loads((PROJECT/'comparator.json').read_text())
if len(config['theorem_names'])!=11 or config['definition_names']!=[]:raise RuntimeError('Expected retained ten exports plus literal intrinsic Target and no holes')
lock={'entry':ENTRY,'literal_intrinsic_target':'NLA.TR06.target : NLA.Statements.TR06.Target',
 'retained_source_count':58,'actual_copied_source_count':len(copies),
 'actual_proof_source_count':sum(x['module'].startswith('NLA.Proofs.TR06.') for x in copies),
 'actual_canonical_Lean_input_count':len(expected_lean),'copies':copies,
 'selected_exports':config['theorem_names'],'package_exports':{name:sha((PROJECT/name).read_bytes()) for name in exports},
 'scope':'Exact source copies and explicit boundary/build exports. Descriptive metadata, review/evidence and actual Linux checking remain separate.'}
p=PROJECT/'proof-source-lock.json'
if args.write:p.write_text(json.dumps(lock,indent=2)+'\n')
elif not p.is_file() or json.loads(p.read_text())!=lock:raise RuntimeError('Proof-source lock differs')
print(json.dumps({'passed':True,'mode':'write' if args.write else 'check','copies':len(copies),'retained':58,'proofs':lock['actual_proof_source_count'],'Lean_inputs':len(expected_lean),'selected_exports':11}))
