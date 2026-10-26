#!/usr/bin/env python3
"""Fresh independent RE06 b48 two-export source replay and actual gate controls.
No author project objects, no Gaussian success/fullTarget/Linux/Comparator claim.
"""
import argparse,hashlib,json,os,re,subprocess,tempfile
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--commit',default='b48de1c1510ec2677ce8300d015e00cdc202065d');p.add_argument('--output',type=Path,required=True);p.add_argument('--lean',type=Path,default=Path('/private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean'));p.add_argument('--packages',type=Path,default=Path('/Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages'));a=p.parse_args();repo=a.repo.resolve();output=a.output.resolve();output.mkdir(parents=True,exist_ok=True)
C='b48de1c1510ec2677ce8300d015e00cdc202065d';assert a.commit==C
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda q:subprocess.check_output(['git','show',C+':'+q],cwd=repo)
manifest=json.loads(read('lean-statements/lake-manifest.json'));checks=[];records=[];error=None;objects={}
def ck(n,v,**x):
 checks.append(dict(name=n,passed=bool(v),**x))
 if not v:raise AssertionError(n)
def deps():
 ans={}
 for pkg in manifest['packages']:
  r=a.packages/pkg['name'];head=subprocess.check_output(['git','-C',str(r),'rev-parse','HEAD']).decode().strip();status=subprocess.check_output(['git','-C',str(r),'status','--porcelain','--untracked-files=normal']).decode();ck('exact-clean-pinned-dependency:'+pkg['name'],head==pkg['rev'] and status=='');ans[pkg['name']]=head
 return ans
modules=['NLA.Computation.SVDMachine','NLA.Computation.NonadaptiveMatrixQuery','NLA.Statements.Infrastructure','NLA.Statements.RE06','Reviewed.RE06','NLA.Proofs.TR04.SVDCore','NLA.Proofs.TR04.SVDTotal','NLA.Proofs.RE06.SVDTotal','NLA.Proofs.RE06.QueryCount','NLA.Proofs.RE06.WidthBounds','NLA.Proofs.RE06.QueryBound','NLA.Proofs.RE06.CountAudit']
source={m:read('lean-statements/'+m.replace('.','/')+'.lean').decode() for m in modules}
selected=[]
for m in modules[5:]:
 ns=[]
 for line in source[m].splitlines():
  if line.startswith('namespace '):ns.append(line[len('namespace '):].strip())
  elif line.startswith('end ') and ns:ns.pop()
  else:
   match=re.match(r'theorem\s+([A-Za-z_][A-Za-z0-9_\']*)',line)
   if match:selected.append('.'.join(ns+[match[1]]))
ck('exact28-source-theorem-declarations-selected',len(selected)==28 and len(set(selected))==28)
public=['NLA.Proofs.RE06.svd_total','NLA.Proofs.RE06.query_bound']
count_support=[n for n in selected if n.startswith('NLA.Proofs.RE06.Counts.')];ck('exact13-count-support-theorems-selected',len(count_support)==13)
body='''import NLA.Proofs.RE06.CountAudit
set_option autoImplicit false
set_option leancert.trust "kernel"
open Lean Elab Command in
elab "#inventory_theorem " n:ident : command => do
  let d ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  match (← getEnv).find? d with
  | some (.thmInfo _) => pure ()
  | _ => throwErrorAt n "inventory expects genuine theorem"
namespace Inventory.RE06
theorem literal_svd_total : NLA.Computation.NonadaptiveMatrixQuery.SVDTotal :=
  NLA.Proofs.RE06.svd_total
theorem literal_query_bound (n m : ℕ) (hn : 0 < n) (ε : ℝ) (hε0 : 0 < ε) (hεh : ε < 1/2) :
  NLA.Computation.NonadaptiveMatrixQuery.QueryBound n m ε 4000000 0 :=
  NLA.Proofs.RE06.query_bound n m hn ε hε0 hεh
theorem live_frozen_identity : NLA.Statements.RE06.Target = NLA.ReviewedStatements.RE06.Target := rfl
end Inventory.RE06
'''
all_selected=selected+['Inventory.RE06.literal_svd_total','Inventory.RE06.literal_query_bound','Inventory.RE06.live_frozen_identity']
for n in all_selected:body+='\n#inventory_theorem '+n+'\n#assert_trust kernel '+n+'\n#print axioms '+n+'\n'
body+='''
open Lean Elab Command in
elab "#inventory_absent " n:ident : command => do
  if (← getEnv).contains n.getId then throwErrorAt n "unexpected completed RE06 export"
#inventory_absent NLA.Proofs.RE06.successful
#inventory_absent NLA.Proofs.RE06.original_claim
#inventory_absent NLA.Proofs.RE06.explicit_claim
#inventory_absent NLA.Proofs.RE06.target
'''
source['Inventory.Audit']=body
negative={
 'Inventory.HoleSVD':('sorryAx','''import NLA.Proofs.RE06.CountAudit
set_option leancert.trust "kernel"
theorem counterfeit : NLA.Computation.NonadaptiveMatrixQuery.SVDTotal := by sorry
#assert_trust kernel counterfeit
'''),
 'Inventory.HoleQuery':('sorryAx','''import NLA.Proofs.RE06.CountAudit
set_option leancert.trust "kernel"
theorem counterfeit (n m : ℕ) (hn : 0<n) (ε : ℝ) (hε0 : 0<ε) (hεh : ε<1/2) : NLA.Computation.NonadaptiveMatrixQuery.QueryBound n m ε 4000000 0 := by sorry
#assert_trust kernel counterfeit
'''),
 'Inventory.DefSVD':('inventory expects genuine theorem','''import Inventory.Audit
def counterfeit := NLA.Proofs.RE06.svd_total
#inventory_theorem counterfeit
'''),
 'Inventory.DefQuery':('inventory expects genuine theorem','''import Inventory.Audit
def counterfeit := NLA.Proofs.RE06.query_bound
#inventory_theorem counterfeit
'''),
 'Inventory.OracleSVD':('oracle','''import NLA.Proofs.RE06.CountAudit
set_option leancert.trust "kernel"
axiom oracle : False
theorem counterfeit : NLA.Computation.NonadaptiveMatrixQuery.SVDTotal := False.elim oracle
#assert_trust kernel counterfeit
'''),
 'Inventory.OracleQuery':('oracle','''import NLA.Proofs.RE06.CountAudit
set_option leancert.trust "kernel"
axiom oracle : False
theorem counterfeit (n m : ℕ) (hn : 0<n) (ε : ℝ) (hε0 : 0<ε) (hεh : ε<1/2) : NLA.Computation.NonadaptiveMatrixQuery.QueryBound n m ε 4000000 0 := False.elim oracle
#assert_trust kernel counterfeit
'''),
 'Inventory.FullReference':('sorryAx',read('docs/lean/proofs/RE-06/campaign-2026-10-26/preproof/Challenge.lean').decode())}
source.update({n:v[1] for n,v in negative.items()})
heads_before={};heads_after={};version=''
try:
 heads_before=deps();version=subprocess.check_output([str(a.lean),'--version']).decode().strip();ck('official-Lean4331-commit', '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version)
 with tempfile.TemporaryDirectory(prefix='nla-re06-counts-inventory-',dir='/private/tmp') as tmp:
  tmp=Path(tmp);srcroot=tmp/'source';objroot=tmp/'objects';srcroot.mkdir();objroot.mkdir()
  for m,b in source.items():
   p=srcroot/(m.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(b)
   kept=output/'sources'/(m.replace('.','/')+'.lean.txt');kept.parent.mkdir(parents=True,exist_ok=True);kept.write_bytes(p.read_bytes())
  env=os.environ.copy();env['LEAN_PATH']=':'.join([str(objroot)]+[str(a.packages/p['name']/'.lake/build/lib/lean') for p in manifest['packages']]+[str(a.lean.parent.parent/'lib/lean')]);env.pop('LEAN_SRC_PATH',None)
  for m in modules+['Inventory.Audit']+list(negative):
   p=srcroot/(m.replace('.','/')+'.lean');obj=objroot/(m.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
   argv=[str(a.lean),'-R',str(srcroot),'-o',str(obj),str(p)];run=subprocess.run(argv,cwd=srcroot,env=env,capture_output=True,text=True,timeout=600);log=run.stdout+run.stderr;(output/(m+'.log')).write_text(log)
   if m in negative:
    passed=run.returncode!=0 and negative[m][0] in log
    if m=='Inventory.FullReference':passed=passed and log.count('error: #assert_trust:')==6
    elif m.startswith('Inventory.Hole') or m.startswith('Inventory.Oracle'):passed=passed and 'error: #assert_trust:' in log
   else:passed=run.returncode==0
   rec=dict(module=m,command=argv,source_sha256=sha(p.read_bytes()),log_sha256=sha(log.encode()),exit_code=run.returncode,expected_negative=m in negative,passed=passed);records.append(rec);print(m,'PASS' if passed else 'FAIL',flush=True);ck('actual-Lean-outcome:'+m,passed)
   if obj.exists():objects[m]=dict(sha256=sha(obj.read_bytes()),bytes=obj.stat().st_size)
   if m=='Inventory.Audit':
    axioms=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log);ck('all31actual-theorem-kind-kernel-axiom-audits',len(axioms)==len(all_selected)==31 and [n for n,x in axioms]==all_selected and all(set(x.strip() for x in xs.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'} for n,xs in axioms))
    for n,xs in axioms:
     if n in public:ck('public-exact-standard3:'+n,set(x.strip() for x in xs.split(','))=={'propext','Classical.choice','Quot.sound'})
 heads_after=deps();ck('dependencies-byte-pins-clean-before-and-after',heads_before==heads_after)
except Exception as e:error=str(e)
report=dict(reviewer='/root/inventory',authored_RE06_proof_sources=[],scope='Fresh independent own project-object replay of exact two RE06 exports and13count supports, no success/fullTarget/Linux/Comparator claim.',commit=C,passed=error is None and len(records)==20 and all(x['passed'] for x in records),error=error,check_count=len(checks),checks=checks,commands=records,expected_commands=20,own_fresh_project_objects=True,project_objects_removed_after_replay=True,lean_version=version,lean_binary_sha256=sha(a.lean.read_bytes()),dependency_heads_before=heads_before,dependency_heads_after=heads_after,selected_theorems=all_selected,object_sha256=objects,driver_sha256=sha(Path(__file__).read_bytes()))
(output/'RESULT.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:report[k] for k in ['passed','error','check_count','expected_commands']}));raise SystemExit(0 if report['passed'] else 1)
