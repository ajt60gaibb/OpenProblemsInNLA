#!/usr/bin/env python3
"""Fresh local AUTHOR kernel replay. This is not an independent review or CI receipt."""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,tempfile,datetime
ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
ap.add_argument('--lean',type=Path,default=Path('/private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean'))
ap.add_argument('--packages',type=Path,default=Path('/Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages'))
a=ap.parse_args();w=a.repo.resolve();o=a.output.resolve();o.mkdir(parents=True,exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=w/'docs/lean/proofs/RE-06/campaign-2026-10-26/preproof';auth=json.loads((p.parent/'IMPLEMENTATION_AUTHORIZATION.json').read_text());assert auth['implementation_authorized']
for name,h in auth['reviewed_packet_hashes'].items():assert sha(p/name)==h
manifest=json.loads((w/'lean-statements/lake-manifest.json').read_text())
def heads():
 r={}
 for q in manifest['packages']:
  h=subprocess.check_output(['git','-C',str(a.packages/q['name']),'rev-parse','HEAD'],text=True).strip();assert h==q['rev'];r[q['name']]=h
 return r
pins=heads();version=subprocess.check_output([str(a.lean),'--version'],text=True).strip();assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
modules=[];seen=set()
def visit(m):
 if m in seen:return
 seen.add(m);src=w/'lean-statements'/(m.replace('.','/')+'.lean')
 for im in re.findall(r'^import (\S+)',src.read_text(),re.M):
  if im.startswith(('NLA.','Reviewed.')):visit(im)
 modules.append(m)
visit('NLA.Proofs.RE06.ActualRepairAudit')
originals=['NLA.Computation.SVDMachine','NLA.Computation.NonadaptiveMatrixQuery','NLA.Statements.Infrastructure','NLA.Statements.RE06','Reviewed.RE06'];reuse=['NLA.Proofs.TR04.SVDCore','NLA.Proofs.TR04.SVDTotal']
for m in originals+reuse:assert m in modules
negative={
'Negative.Holes':'''import NLA.Proofs.RE06.ActualRepairAudit
set_option leancert.trust "kernel"
open NLA.Computation.NonadaptiveMatrixQuery NLA.Proofs.RE06 NLA.Proofs.RE06.Repair
theorem fake_error {n k c ell : ℕ} (Y : Matrix (Fin n) (Fin k) ℝ)
 (C : Matrix (Fin n) (Fin c) ℝ) (Ht : Matrix (Fin ell) (Fin n) ℝ) :
 squaredFrobenius (C-Y*pseudoInverse (Ht*Y)*(Ht*C)) 0 =
 squaredFrobenius (actualRangeResidual Y C) 0+actualRegressionEnergy Y C Ht := by sorry
#assert_trust kernel fake_error
theorem fake_meas {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (k ell r : ℕ) (η:ℝ) :
 MeasurableSet (repairFailureSet C k ell r η) := by sorry
#assert_trust kernel fake_meas
''',
'Negative.DefinitionAlias':'''import NLA.Proofs.RE06.ActualRepairAudit
def counterfeit := @NLA.Proofs.RE06.Repair.actual_svd_repair_majorant
#repair_theorem counterfeit
''',
'Negative.CustomAxiom':'''import NLA.Proofs.RE06.ActualRepairAudit
axiom counterfeit : NLA.Computation.NonadaptiveMatrixQuery.SVDTotal
theorem forged : NLA.Computation.NonadaptiveMatrixQuery.SVDTotal := counterfeit
#assert_trust kernel forged
''',
'Negative.DroppedRank':'''import NLA.Proofs.RE06.ActualRepairAudit
open NLA.Computation.NonadaptiveMatrixQuery NLA.Proofs.RE06 NLA.Proofs.RE06.Repair
example {n k : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)(r:ℕ)(hr:r≤n)(G:Matrix (Fin n) (Fin k) ℝ) :
 squaredFrobenius (actualRangeResidual (C*G) C) 0≤residualTailEnergy C r+tailRandomEnergy C r hr G := by
 exact actual_rangefinder_majorant C r hr G
'''}
inputs=[];records=[]
with tempfile.TemporaryDirectory(prefix='nla-re06-actual-replay-',dir='/private/tmp') as td:
 td=Path(td);source=td/'source';out=td/'out';source.mkdir();out.mkdir();assert not list(out.iterdir())
 for m in modules:
  rel=Path(m.replace('.','/')+'.lean');src=w/'lean-statements'/rel
  if m in originals:assert src.read_bytes()==(p/'originals/lean-statements'/rel).read_bytes()
  if m in reuse:assert src.read_bytes()==(p/'supplementary-reuse/lean-statements'/rel).read_bytes()
  if m.startswith('NLA.Proofs.RE06.'):assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',src.read_text())
  dst=source/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(src.read_bytes())
  inputs.append({'module':m,'path':'lean-statements/'+str(rel),'sha256':sha(src),'bytes':src.stat().st_size})
 for m,s in negative.items():
  dst=source/(m.replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);dst.write_text(s)
 env=os.environ.copy();env['LEAN_PATH']=':'.join([str(out)]+[str(q/'.lake/build/lib/lean') for q in sorted(a.packages.iterdir()) if (q/'.lake/build/lib/lean').is_dir()]+[str(a.lean.parent.parent/'lib/lean')])
 for m in modules+list(negative):
  src=source/(m.replace('.','/')+'.lean');obj=out/(m.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
  argv=[str(a.lean),'-R',str(source),'-o',str(obj),str(src)]
  r=subprocess.run(argv,cwd=source,env=env,capture_output=True,text=True,timeout=600);log=r.stdout+r.stderr
  if m=='Negative.Holes':ok=r.returncode!=0 and log.count('error: #assert_trust:')==2 and 'sorryAx' in log
  elif m=='Negative.DefinitionAlias':ok=r.returncode!=0 and 'expected actual theorem declaration' in log
  elif m=='Negative.CustomAxiom':ok=r.returncode!=0 and 'error: #assert_trust:' in log and 'counterfeit' in log
  elif m=='Negative.DroppedRank':ok=r.returncode!=0 and 'Type mismatch' in log
  else:ok=r.returncode==0
  dst=o/'sources'/(m.replace('.','/')+'.lean.txt');dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(src.read_bytes());(o/(m+'.log')).write_text(log)
  records.append({'module':m,'argv':argv,'source_sha256':sha(src),'exit_code':r.returncode,'negative':m in negative,'passed':ok})
  print(m,'PASS' if ok else 'FAIL',flush=True)
  if not ok:print(log,flush=True);break
 assert heads()==pins
 audit=(o/'NLA.Proofs.RE06.ActualRepairAudit.log').read_text() if (o/'NLA.Proofs.RE06.ActualRepairAudit.log').exists() else ''
 ax=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit,re.S)
 allstd=all(set(re.sub(r'\s','',s).split(','))<=set(['propext','Classical.choice','Quot.sound']) for _,s in ax)
 report={'scope':'AUTHOR ONLY: actual deterministic SVD partition, rangefinder majorant and globally measurable basis-free excess; no probability expectation/full Target/independent review/CI/Comparator approval','UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'base_commit':subprocess.check_output(['git','-C',str(w),'rev-parse','HEAD'],text=True).strip(),'lean_version':version,'lean_sha256':sha(a.lean),'dependency_heads_before_and_after':pins,'fresh_project_objects':True,'objects_removed_after_replay':True,'inputs':inputs,'records':records,'audited_new_support_theorems':41,'audited_functional_definitions':14,'axiom_audit_lines':len(ax),'standard_only':allstd,'passed':len(records)==len(modules)+len(negative) and all(r['passed'] for r in records) and len(ax)==55 and allstd}
 (o/'RESULT.json').write_text(json.dumps(report,indent=2)+'\n')
print('expected outcomes',len(modules)+len(negative),'fresh sources',len(modules),'accepted',report['passed'],flush=True)
raise SystemExit(0 if report['passed'] else 1)
