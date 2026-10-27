#!/usr/bin/env python3
"""Run the real pinned Comparator signature/axiom library on local environments.

This is no exporter CLI, Linux sandbox, raw-kernel replay or CI receipt.
"""
import argparse,hashlib,json,os,subprocess
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
for n in ['repo','package-objects','checker-source','lean','packages','output']:p.add_argument('--'+n,type=Path,required=True)
p.add_argument('--commit',required=True)
a=p.parse_args()
for k,v in vars(a).items():
 if isinstance(v,Path): setattr(a,k,v.resolve())
a.output.mkdir(parents=True,exist_ok=False);source=a.output/'source';objects=a.output/'objects';source.mkdir();objects.mkdir()
C=a.commit;sha=lambda b:hashlib.sha256(b).hexdigest()
lock=json.loads(subprocess.check_output(['git','show',C+':tools/lean/source-lock.json'],cwd=a.repo))
records=[];sources={}
env=os.environ.copy();env['PATH']=str(a.lean.parent)+os.pathsep+env.get('PATH','');env['LEAN_PATH']=':'.join([str(objects),str(a.package_objects)]+[str(q/'.lake/build/lib/lean') for q in sorted(a.packages.iterdir()) if (q/'.lake/build/lib/lean').is_dir()]+[str(a.lean.parent.parent/'lib/lean')])
def run(name,argv):
 r=subprocess.run(argv,cwd=source,env=env,text=True,capture_output=True,timeout=600);log=r.stdout+r.stderr;(a.output/(name+'.log')).write_text(log)
 records.append(dict(name=name,argv=argv,exit_code=r.returncode,log_sha256=sha(log.encode())))
 assert r.returncode==0,log
 return log
for rel in ['Comparator/Util.lean','Export/Parse.lean','Comparator/Axioms.lean','Comparator/Compare.lean']:
 b=(a.checker_source/rel).read_bytes();matches=[x for x in lock['files'] if x['sha256']==sha(b) and x['bytes']==len(b)]
 assert len(matches)==1,rel
 sources[rel]=dict(sha256=sha(b),bytes=len(b),source_lock_record=matches[0]);f=source/rel;f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b);o=objects/Path(rel).with_suffix('.olean');o.parent.mkdir(parents=True,exist_ok=True)
 run(rel.replace('/','-'),[str(a.lean),'-R',str(source),'-o',str(o),str(f)])
consumer='''import Lean
import Comparator.Compare
open Lean
def imported (moduleName : Name) : IO Export.ExportedEnv := do
  let env ← importModules #[{ module := moduleName }] {} 0
  let consts := env.constants.toList
  return { constMap := Std.HashMap.ofList consts, constOrder := (consts.map Prod.fst).toArray }
def requireSuccess (label : String) (result : Except String Unit) : IO Unit := do
  match result with
  | .ok _ => IO.println s!"PASS {label}"
  | .error err => throw <| IO.userError s!"{label}: unexpected rejection: {err}"
def requireReject (label expected : String) (result : Except String Unit) : IO Unit := do
  match result with
  | .ok _ => throw <| IO.userError s!"{label}: invalid comparison accepted"
  | .error err =>
    unless (err.splitOn expected).length > 1 do
      throw <| IO.userError s!"{label}: wrong rejection: {err}"
    IO.println s!"PASS {label}: {err}"
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let challenge ← imported `Challenge
  let solution ← imported `Solution
  let targets := #[`NLA.Proofs.TR26.nonisotropic_degree, `NLA.Proofs.TR26.isotropic_degree, `NLA.Proofs.TR26.target]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  requireSuccess "all three exact canonical signatures and referenced definitions" <|
    Comparator.compareAt challenge solution targets #[] #[]
  requireSuccess "all three transitive standard-only axiom closures" <|
    Comparator.checkAxioms solution targets #[] allowed
  for target in targets do
    let some (.thmInfo v) := solution.constMap[target]?
      | throw <| IO.userError "actual solution endpoint is not a theorem"
    let wrongInfo : ConstantInfo := .thmInfo { v with type := .const ``True [] }
    let wrongStatement := { solution with constMap := solution.constMap.insert target wrongInfo }
    requireReject s!"changed statement rejected: {target}" "theorem statement do not match" <|
      Comparator.compareAt challenge wrongStatement #[target] #[] #[]
    let wrongKindInfo : ConstantInfo := .axiomInfo { toConstantVal := v.toConstantVal, isUnsafe := false }
    let wrongKind := { solution with constMap := solution.constMap.insert target wrongKindInfo }
    requireReject s!"changed declaration kind rejected: {target}" "constant kind don't match" <|
      Comparator.compareAt challenge wrongKind #[target] #[] #[]
    let oracleName := `InventoryComparatorOracle
    let oracleInfo : ConstantInfo := .axiomInfo { name := oracleName, levelParams := v.levelParams, type := v.type, isUnsafe := false }
    let oracleProofInfo : ConstantInfo := .thmInfo { v with value := .const oracleName [] }
    let oracleMap := (solution.constMap.insert oracleName oracleInfo).insert target oracleProofInfo
    let oracleSolution := { solution with constMap := oracleMap }
    requireReject s!"custom exact-typed oracle proof rejected: {target}" "Illegal axiom detected" <|
      Comparator.checkAxioms oracleSolution #[target] #[] allowed
    requireReject s!"original reference hole rejected: {target}" "Illegal axiom detected" <|
      Comparator.checkAxioms challenge #[target] #[] allowed
  IO.println "PASS all fourteen actual Comparator-library signature/axiom cases"
'''
f=source/'ComparePackage.lean';f.write_text(consumer);log=run('ComparePackage',[str(a.lean),'--run',str(f)])
assert 'PASS all fourteen actual Comparator-library signature/axiom cases' in log
r=dict(scope=__doc__,reviewer='/root/inventory',immutable_package_commit=C,passed=True,actual_Comparator_library_called=True,exporter_CLI_executed=False,Linux_sandbox=False,raw_kernel_replay=False,CI=False,theorem_targets=['NLA.Proofs.TR26.nonisotropic_degree','NLA.Proofs.TR26.isotropic_degree','NLA.Proofs.TR26.target'],definition_targets=[],permitted_axioms=['propext','Classical.choice','Quot.sound'],fourteen_cases_pass=True,source_lock_commit=lock['commit'],source_lock_sha256=sha(subprocess.check_output(['git','show',C+':tools/lean/source-lock.json'],cwd=a.repo)),sources=sources,consumer_sha256=sha(consumer.encode()),records=records,driver_sha256=sha(Path(__file__).read_bytes()))
(a.output/'result.json').write_text(json.dumps(r,indent=2)+'\n');print('PASS actual pinned Comparator library: all three exact signatures/definitions, standard axioms and twelve negative comparisons')
