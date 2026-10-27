#!/usr/bin/env python3
"""Fresh local AUTHOR source replay. Author Linux/Comparator acceptance is a separate gate."""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,tempfile,datetime
ap=argparse.ArgumentParser();ap.add_argument('--lean',type=Path,required=True);ap.add_argument('--packages',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
p=Path(__file__).resolve().parent;o=a.output.resolve();o.mkdir(parents=True,exist_ok=False)
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
lock=json.loads((p/'PACKAGE_LOCK.json').read_text());expected=set(lock['files'])|{'PACKAGE_LOCK.json'}
actual={str(q.relative_to(p)) for q in p.rglob('*') if q.is_file() and not any(z in ['.git','.lake'] for z in q.relative_to(p).parts)}
assert actual==expected,(sorted(actual-expected),sorted(expected-actual))
for f,r in lock['files'].items():assert sha(p/f)==r['sha256'] and (p/f).stat().st_size==r['bytes'],f
mapping=json.loads((p/'SOURCE_MAP.json').read_text())
for r in mapping['copies']:assert sha(p/r['path'])==r['sha256'] and (p/r['path']).stat().st_size==r['bytes']
derivation=json.loads((p/'CHALLENGE_DERIVATION.json').read_text());original=(p/derivation['original']['path']).read_text();removed=derivation['removed_lines']
assert hashlib.sha256(original.encode()).hexdigest()==derivation['original']['sha256'] and len(removed)==12
assert (p/'Challenge.lean').read_text()=='\n'.join(s for s in original.splitlines() if s not in removed)+'\n'
assert sha(p/'Challenge.lean')==derivation['canonical_reference_sha256']
config=json.loads((p/'comparator.json').read_text());exports=json.loads((p/'reviews/preproof/EXPORTS.json').read_text())['exports']
assert config['definition_names']==[] and config['theorem_names']==['NLA.Proofs.RE06.'+r['name'] for r in exports] and len(exports)==6
manifest=json.loads((p/'lake-manifest.json').read_text())
def heads():
 result={}
 for r in manifest['packages']:
  h=subprocess.check_output(['git','-C',str(a.packages/r['name']),'rev-parse','HEAD'],text=True).strip();assert h==r['rev'];result[r['name']]=h
 return result
pins=heads();version=subprocess.check_output([str(a.lean),'--version'],text=True).strip();assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
order=mapping['runtime_lean_order'];assert len(order)==91 and len(set(order))==91
negative=[('controls/ChallengeTrustRejection.lean.txt','Negative.ChallengeTrust'),('controls/DefinitionKindRejection.lean.txt','Negative.DefinitionKind'),('controls/CustomAxiomRejection.lean.txt','Negative.CustomAxiom')]
records=[]
with tempfile.TemporaryDirectory(prefix='nla-re06-canonical-replay-',dir='/private/tmp') as temp:
 temp=Path(temp);source=temp/'source';out=temp/'out';source.mkdir();out.mkdir();assert not list(out.iterdir())
 for f in order:
  dst=source/f;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes((p/f).read_bytes())
 for f,m in negative:
  dst=source/(m.replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes((p/f).read_bytes())
 env=os.environ.copy();env['LEAN_PATH']=':'.join([str(out)]+[str(q/'.lake/build/lib/lean') for q in sorted(a.packages.iterdir()) if (q/'.lake/build/lib/lean').is_dir()]+[str(a.lean.parent.parent/'lib/lean')])
 jobs=[(f,f.removesuffix('.lean').replace('/','.')) for f in order]+[(m.replace('.','/')+'.lean',m) for _,m in negative]
 for f,m in jobs:
  src=source/f;obj=out/(m.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
  argv=[str(a.lean),'-R',str(source),'-o',str(obj),str(src)];r=subprocess.run(argv,cwd=source,env=env,capture_output=True,text=True,timeout=900);log=r.stdout+r.stderr
  if m=='Negative.ChallengeTrust':ok=r.returncode!=0 and log.count('error: #assert_trust:')==6 and 'sorryAx' in log and 'Unknown' not in log
  elif m=='Negative.DefinitionKind':ok=r.returncode!=0 and 'expected actual theorem declaration' in log and 'Unknown' not in log
  elif m=='Negative.CustomAxiom':ok=r.returncode!=0 and 'error: #assert_trust:' in log and 'PackageOracle' in log and 'Unknown' not in log
  else:ok=r.returncode==0
  dst=o/'sources'/(f+'.txt');dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(src.read_bytes());(o/(m+'.log')).write_text(log)
  records.append({'module':m,'argv':argv,'source_sha256':sha(src),'exit_code':r.returncode,'negative':m.startswith('Negative.'),'passed':ok})
  print(m,'PASS' if ok else 'FAIL',flush=True)
  if not ok:print(log,flush=True);break
 assert heads()==pins
 audit=(o/'EndpointAudit.log').read_text() if (o/'EndpointAudit.log').exists() else ''
 ax=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit,re.S);std={'propext','Classical.choice','Quot.sound'}
 exact=all(set(re.sub(r'\s','',s).split(','))==std for _,s in ax)
 good=len(records)==94 and all(x['passed'] for x in records) and len(ax)==6 and exact
 report={'scope':'Local AUTHOR canonical source/kernel replay, not independent review, actual Linux isolation or Comparator acceptance','UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'proof_source_ref':mapping['proof_source_ref'],'package_lock_sha256':sha(p/'PACKAGE_LOCK.json'),'copied_source_files':87,'fresh_runtime_inputs':91,'negative_commands':3,'expected_outcomes':94,'lean_version':version,'lean_executable_sha256':sha(a.lean),'dependency_heads_before_and_after':pins,'initial_project_objects_empty':True,'borrowed_project_objects':False,'temporary_objects_removed_after_replay':True,'records':records,'endpoint_axiom_lines':len(ax),'all_six_exact_standard_axioms':exact,'passed':good}
 (o/'RESULT.json').write_text(json.dumps(report,indent=2)+'\n')
print('Fresh canonical author replay',good,len(records),'of94 expected outcomes',flush=True)
raise SystemExit(0 if good else 1)
