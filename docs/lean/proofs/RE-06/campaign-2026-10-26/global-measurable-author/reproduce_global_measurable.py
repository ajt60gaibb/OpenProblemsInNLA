#!/usr/bin/env python3
"""Author-only fresh replay of actual pseudoinverse and reciprocal Gaussian norm support.

This is not independent review, whole-problem verification, Linux CI or a
Comparator receipt. The rectangular pseudoinverse moment and final success proof remain outside this scope.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,tempfile

ap=argparse.ArgumentParser()
ap.add_argument('--repo',type=Path,required=True)
ap.add_argument('--output',type=Path,required=True)
ap.add_argument('--freeze',type=Path,default=Path(__file__).resolve().parent/'SOURCE_FREEZE.json')
ap.add_argument('--lean',type=Path,default=Path('/private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean'))
ap.add_argument('--packages',type=Path,default=Path('/Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages'))
a=ap.parse_args();repo=a.repo.resolve();output=a.output.resolve();output.mkdir(parents=True,exist_ok=True)
packet=repo/'docs/lean/proofs/RE-06/campaign-2026-10-26/preproof'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
authorization=json.loads((packet.parent/'IMPLEMENTATION_AUTHORIZATION.json').read_text())
assert authorization['implementation_authorized'] is True
for name,expected in authorization['reviewed_packet_hashes'].items():assert sha(packet/name)==expected,name
manifest=json.loads((repo/'lean-statements/lake-manifest.json').read_text())
def dependency_heads():
 heads={}
 for pkg in manifest['packages']:
  head=subprocess.check_output(['git','-C',str(a.packages/pkg['name']),'rev-parse','HEAD'],text=True).strip()
  assert head==pkg['rev'],(pkg['name'],head,pkg['rev']);heads[pkg['name']]=head
 return heads
heads=dependency_heads()
frozen=json.loads(a.freeze.read_text())
for row in frozen['files']:
 assert sha(repo/row['path'])==row['sha256'],row['path']
version=subprocess.check_output([str(a.lean),'--version'],text=True).strip()
assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version,version
originals=['NLA.Computation.SVDMachine','NLA.Computation.NonadaptiveMatrixQuery','NLA.Statements.Infrastructure','NLA.Statements.RE06','Reviewed.RE06']
reuse=['NLA.Proofs.TR04.SVDCore','NLA.Proofs.TR04.SVDTotal']
upstream=['NLA.Proofs.RE06.SVDTotal','NLA.Proofs.RE06.GaussianStream','NLA.Proofs.RE06.GaussianLaplace','NLA.Proofs.RE06.GaussianQuadratic','NLA.Proofs.RE06.GaussianRotation']
proofs=['NLA.Proofs.RE06.PseudoInverseCore', 'NLA.Proofs.RE06.PseudoInverseIdentities', 'NLA.Proofs.RE06.PseudoInverseUnique', 'NLA.Proofs.RE06.PseudoInverseFullRank', 'NLA.Proofs.RE06.PseudoInverseProduct', 'NLA.Proofs.RE06.PseudoInverseRange', 'NLA.Proofs.RE06.PseudoInverseMeasurable', 'NLA.Proofs.RE06.PseudoInverseRankEvents', 'NLA.Proofs.RE06.GaussianMomentAlgebra', 'NLA.Proofs.RE06.GaussianMomentGamma', 'NLA.Proofs.RE06.GaussianMomentLaplace', 'NLA.Proofs.RE06.GaussianMomentNorm', 'NLA.Proofs.RE06.GaussianMomentProjection', 'NLA.Proofs.RE06.PseudoInverseAudit', 'NLA.Proofs.RE06.GaussianMomentPolynomialNull', 'NLA.Proofs.RE06.GaussianMomentFullRank', 'NLA.Proofs.RE06.GaussianMomentFullRankAudit', 'NLA.Proofs.RE06.PseudoInverseTikhonovCore', 'NLA.Proofs.RE06.PseudoInverseTikhonovLimit', 'NLA.Proofs.RE06.PseudoInverseGlobalMeasurable', 'NLA.Proofs.RE06.PseudoInverseGlobalAudit']
inputs=[];records=[]
with tempfile.TemporaryDirectory(prefix='nla-re06-counts-replay-',dir='/private/tmp') as tmp:
 tmp=Path(tmp);source=tmp/'source';out=tmp/'out';source.mkdir();out.mkdir()
 for module in originals+reuse+upstream+proofs:
  rel=Path(module.replace('.','/')+'.lean');src=repo/'lean-statements'/rel
  if module in originals:assert src.read_bytes()==(packet/'originals/lean-statements'/rel).read_bytes(),str(rel)
  if module in reuse:assert src.read_bytes()==(packet/'supplementary-reuse/lean-statements'/rel).read_bytes(),str(rel)
  dst=source/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(src.read_bytes())
  inputs.append({'path':str(Path('lean-statements')/rel),'sha256':sha(src),'bytes':src.stat().st_size,'role':'unchanged published' if module in originals else 'unchanged reviewed SVD reuse' if module in reuse else 'previous author support' if module in upstream else 'new author proof/audit'})
  if module in proofs:
   assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',src.read_text()),str(rel)
 negatives={
 'Negative.Holes':'''import NLA.Proofs.RE06.PseudoInverseAudit
set_option leancert.trust "kernel"
namespace Negative
theorem fake_svd : NLA.Computation.NonadaptiveMatrixQuery.SVDTotal := by sorry
theorem fake_count (n m : ℕ) (hn : 0<n) (ε : ℝ) (hε0 : 0<ε) (hεh : ε<1/2) :
 NLA.Computation.NonadaptiveMatrixQuery.QueryBound n m ε 4000000 0 := by sorry
#assert_trust kernel fake_svd
#assert_trust kernel fake_count
end Negative
''',
 'Negative.DefinitionAlias':'''import NLA.Proofs.RE06.PseudoInverseAudit
def counterfeit := @NLA.Proofs.RE06.Pseudo.actual_isMP
#actual_theorem counterfeit
''',
 'Negative.CustomAxiom':'''import NLA.Proofs.RE06.PseudoInverseAudit
axiom counterfeit : NLA.Computation.NonadaptiveMatrixQuery.SVDTotal
theorem forged : NLA.Computation.NonadaptiveMatrixQuery.SVDTotal := counterfeit
#assert_trust kernel forged
'''}
 for module,body in negatives.items():
  dst=source/(module.replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);dst.write_text(body)
 env=os.environ.copy();env['LEAN_PATH']=':'.join([str(out)]+[str(p/'.lake/build/lib/lean') for p in sorted(a.packages.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]+[str(a.lean.parent.parent/'lib/lean')])
 for module in originals+reuse+upstream+proofs+list(negatives):
  src=source/(module.replace('.','/')+'.lean');obj=out/(module.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
  argv=[str(a.lean),'-R',str(source),'-o',str(obj),str(src)]
  p=subprocess.run(argv,cwd=source,env=env,capture_output=True,text=True,timeout=600);log=p.stdout+p.stderr
  if module=='Negative.Holes':passed=p.returncode!=0 and log.count('error: #assert_trust:')==2 and 'sorryAx' in log
  elif module=='Negative.DefinitionAlias':passed=p.returncode!=0 and 'expected actual theorem declaration' in log
  elif module=='Negative.CustomAxiom':passed=p.returncode!=0 and 'error: #assert_trust:' in log and 'counterfeit' in log
  else:passed=p.returncode==0
  dest=output/'sources'/(module.replace('.','/')+'.lean.txt');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(src.read_bytes())
  (output/(module+'.log')).write_text(log)
  rec={'module':module,'argv':argv,'source_sha256':sha(src),'exit_code':p.returncode,'negative':module in negatives,'passed':passed};records.append(rec)
  print(module,'PASS' if passed else 'FAIL',flush=True)
  if not passed:print(log,flush=True);break
assert dependency_heads()==heads
report={'scope':'AUTHOR ONLY: global actual pseudoinverse Borel measurability with prior full-rank/MP/projected-moment foundation, no rectangular inverse-Wishart/success/full Target/independent approval/CI/Comparator claim','implementation_authorization_sha256':sha(packet.parent/'IMPLEMENTATION_AUTHORIZATION.json'),'lean_version':version,'lean_sha256':sha(a.lean),'external_dependency_heads_before_and_after':heads,'fresh_project_objects':True,'project_objects_removed_after_replay':True,'source_freeze_sha256':sha(a.freeze),'inputs':inputs,'records':records,'passed':len(records)==36 and all(x['passed'] for x in records)}
(output/'RESULT.json').write_text(json.dumps(report,indent=2)+'\n')
raise SystemExit(0 if report['passed'] else 1)
