"""Archive and audit actual successful local runs, following exact reuse receipts.
No compiler, Comparator, network, or publication is performed by this script.
Arguments: PROBLEM RUN PACKET_DIRECTORY
"""
from pathlib import Path
import datetime,gzip,hashlib,json,re,shutil,sys
D=Path(__file__).resolve().parents[1];L=D/'local-lean'
problem,run_name,packet=sys.argv[1:];P=Path(packet).resolve();assert P.is_relative_to(D)
OUT=D/'verification'/f'{problem}-local-20260919';OUT.mkdir(parents=True,exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts={}
def read_receipt(path,expected=None):
 path=Path(path);raw=path.read_bytes();digest=hashlib.sha256(raw).hexdigest()
 if expected:assert digest==expected,(path,digest,expected)
 obj=json.loads(raw);assert obj.get('end');receipts[path.parent.name]=(raw,digest);return obj
rpath=L/'runs'/run_name/'RECEIPT.json';top=read_receipt(rpath)
seen=set()
def visit(mod):
 rel=mod.replace('.','/')+'.lean';f=P/rel
 if not f.is_file() or mod in seen:return
 seen.add(mod)
 for line in f.read_text().splitlines():
  if line.startswith('import '):
   for dep in line[7:].split():visit(dep)
visit('Solution');commands=[c for c in top['commands'] if c['module'] in seen]
assert {c['module'] for c in commands}==seen
outputs={c['module']:c['output_sha256'] for c in commands};records=[]
for initial in commands:
 module=initial['module'];rel=module.replace('.','/')+'.lean';source_hash=sha(P/rel)
 assert source_hash==initial['source_sha256']
 candidates=[L/'.lake/build/lib/lean'/(module.replace('.','/')+'.olean')]
 candidates += list((L/'source-archives').glob('*/outputs/'+module.replace('.','/')+'.olean'))
 assert any(p.exists() and sha(p)==initial['output_sha256'] for p in candidates),(module,'no actual matching output')
 c,run,chain=initial,run_name,[];visited=set()
 while c.get('status')=='reused_exact_successful_local_output':
  assert run not in visited;visited.add(run)
  for name,digest in c['transitive_source_hashes'].items():assert sha(P/name)==digest,(module,name)
  priorpath=Path(c['prior_receipt']);prior=read_receipt(priorpath,c['prior_receipt_sha256'])
  chain.append({'run':run,'prior':priorpath.parent.name,'prior_receipt_sha256':c['prior_receipt_sha256']})
  matches=[v for v in prior['commands'] if v['module']==module];assert len(matches)==1
  c,run=matches[0],priorpath.parent.name
  assert c['source_sha256']==source_hash and c['output_sha256']==initial['output_sha256']
 assert c['exit_code']==0,(module,run)
 assert '--threads=1' in c['argv'] and '--memory=4096' in c['argv']
 for dep,digest in c.get('dependency_olean_sha256',{}).items():assert outputs[dep]==digest,(module,dep)
 log=L/'runs'/run/(module+'.log');assert sha(log)==c['log_sha256']
 dest=OUT/'logs'/run/log.name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(log,dest)
 records.append({'module':module,'source':rel,'source_sha256':source_hash,'output_sha256':initial['output_sha256'],'reuse_chain':chain,'fresh_success_run':run,'actual_fresh_command':c,'log':str(dest.relative_to(OUT))})
log=(L/'runs'/run_name/'Solution.log').read_text();names=json.loads((P/'comparator.json').read_text())['theorem_names']
axioms={n:a.split(', ') if a else [] for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)}
assert set(axioms)==set(names);assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in axioms.values())
(OUT/'actual-axioms.json').write_text(json.dumps(axioms,indent=2)+'\n')
index={}
for run,(raw,digest) in sorted(receipts.items()):
 dest=OUT/'receipts'/(run+'.RECEIPT.json.gz');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(gzip.compress(raw,mtime=0));index[run]={'file':str(dest.relative_to(OUT)),'original_sha256':digest,'gzip_sha256':sha(dest)}
for name in ['serial_compile_recovery.py','LOCAL-ENVIRONMENT.json']:shutil.copyfile(L/name,OUT/name)
audit={'time':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':f'Actual macOS {problem} local compiler outputs and recursively checked reuse origins only','new_Lean_run_by_archiver':False,'standalone_lake_build':'NOT_RUN; actual direct serial commands recorded verbatim','GitHub_Comparator':'NOT_RUN_FOR_THIS_PROBLEM','aggregate_run':run_name,'aggregate_receipt_sha256':sha(rpath),'aggregate_command':next(c for c in commands if c['module']=='Solution'),'fresh_aggregate_and_reused_module_count':len(commands),'kernel_trust_assertions_and_actual_axiom_reports':len(axioms),'compiler_sha256':top['compiler_sha256'],'runner_sha256':top['runner_sha256'],'resource_limits':{'compiler_processes':1,'threads':1,'memory_MiB':4096},'module_records':records,'lossless_original_receipts':index,'mixed_run_warning':'Original receipts may include other problems and failures. Only the listed successful exact-source commands support this audit. Challenge placeholders are not proof evidence.','count_increment':0}
(OUT/'LOCAL-REPLAY-AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n')
print(problem,'actualproofmodules',len(records),'contracts',len(axioms),'auditsha',sha(OUT/'LOCAL-REPLAY-AUDIT.json'))
