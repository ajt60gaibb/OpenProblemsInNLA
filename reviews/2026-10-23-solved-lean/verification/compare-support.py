#!/usr/bin/env python3
"""Independently replay a frozen support packet and compare separate Lean environments.

Uses unchanged, SHA-256-locked Comparator library code. No Linux executable,
exporter, sandbox, or separate raw-kernel replay is performed by this script.
"""
from __future__ import annotations
import argparse
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
ARCHIVE = ROOT/'eigenvalues-and-inverse-problems/IS-03/lean/verification/linux-2026-09-12/source/forsythe'
PINNED = [('.tools/lean4export/Export/Parse.lean','Export/Parse.lean'),
          ('.tools/comparator/Comparator/Util.lean','Comparator/Util.lean'),
          ('.tools/comparator/Comparator/Axioms.lean','Comparator/Axioms.lean'),
          ('.tools/comparator/Comparator/Compare.lean','Comparator/Compare.lean')]
def sha(path):
    return hashlib.file_digest(Path(path).open('rb'),'sha256').hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lean',type=Path,required=True)
    ap.add_argument('--packages',type=Path,required=True)
    ap.add_argument('--packet',type=Path,required=True)
    ap.add_argument('--config',type=Path,required=True)
    args=ap.parse_args()
    config=json.loads(args.config.read_text())
    for n in [config['challenge_module'],config['solution_module'],*config['theorem_names']]:
        if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*',n):
            raise RuntimeError('invalid Lean module/name')
    lean=args.lean.resolve();packages=args.packages.resolve();packet=args.packet.resolve()
    evidence=HERE/'actual-comparisons';evidence.mkdir(exist_ok=True)
    attempt=Path(tempfile.mkdtemp(prefix='attempt-',dir=evidence));source=attempt/'source';source.mkdir()
    build=Path(tempfile.mkdtemp(prefix='nla-oct23-actual-comparison-'))
    result={'scope':__doc__,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'platform':platform.platform(),'packet':str(packet),'config':config,'source_sha256':{},
            'script_sha256':sha(__file__),'commands':[],'pass':False,'theorem_comparisons':0,
            'comparator_core_executed':False,'full_comparator_executed':False,
            'raw_kernel_replay_executed':False,'exporter_executed':False,
            'authoritative_linux_sandbox':False,'full_ra05_target_proved':False}
    manifest=json.loads((HERE/'published-tooling/lean-statements/lake-manifest.json').read_text())
    env=os.environ.copy();env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
    env['LEAN_PATH']=os.pathsep.join([str(build)]+[str(packages/p['name']/'.lake/build/lib/lean') for p in manifest['packages']]+[str(lean.parent.parent/'lib/lean')])
    def dependencies():
        records=[]
        for p in manifest['packages']:
            directory=packages/p['name']
            head=subprocess.run(['git','-C',str(directory),'rev-parse','HEAD'],text=True,capture_output=True)
            status=subprocess.run(['git','-C',str(directory),'status','--porcelain','--untracked-files=no'],text=True,capture_output=True)
            ok=head.returncode==status.returncode==0 and head.stdout.strip()==p['rev'] and not status.stdout.strip()
            records.append({'name':p['name'],'directory':str(directory),'expected':p['rev'],
                            'actual':head.stdout.strip(),'tracked_status':status.stdout,'ok':ok})
        if not all(p['ok'] for p in records):
            raise RuntimeError('dependency pin or tracked-source cleanliness failed')
        return records
    def run(rel,execute=False):
        artifact=build/Path(rel).with_suffix('.olean');artifact.parent.mkdir(parents=True,exist_ok=True)
        argv=[str(lean),'--run',rel] if execute else [str(lean),'-R',str(source),'-o',str(artifact),rel]
        start=time.monotonic();cp=subprocess.run(argv,cwd=source,env=env,text=True,capture_output=True,timeout=300)
        log=attempt/(rel.replace('/','-')+'.log');log.write_text(cp.stdout+cp.stderr)
        result['commands'].append({'argv':argv,'exit_code':cp.returncode,'elapsed_seconds':time.monotonic()-start,'stdout':cp.stdout,'stderr':cp.stderr,'log_sha256':sha(log)})
        print(rel,cp.returncode,flush=True)
        if cp.returncode:
            raise RuntimeError('command failed: '+rel)
        return cp.stdout
    try:
        result['dependencies_before']=dependencies()
        shutil.copyfile(__file__,source/'compare-support.py')
        cp=subprocess.run([str(lean),'--version'],text=True,capture_output=True)
        result.update(lean_version=cp.stdout.strip(),lean_executable_sha256=sha(lean))
        if cp.returncode or 'version 4.33.1,' not in cp.stdout:
            raise RuntimeError('expected pinned Lean 4.33.1')
        lock=json.loads((HERE/'published-tooling/tools/lean/source-lock.json').read_text())
        bydest={e['destination']:e for e in lock['files']}
        for old,new in PINNED+[('.tools/comparator/LICENSE','LICENSE-COMPARATOR')]:
            src=ARCHIVE/old;dst=source/new;entry=bydest[old]
            if sha(src)!=entry['sha256'] or src.stat().st_size!=entry['bytes']:
                raise RuntimeError('pinned Comparator source mismatch')
            dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
        for rel in config['sources']:
            p=Path(rel)
            if p.is_absolute() or '..' in p.parts or p.suffix!='.lean':
                raise RuntimeError('invalid support source path')
            dest=source/p;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(packet/p,dest)
            result['source_sha256'][rel]=sha(dest)
        spec=importlib.util.spec_from_file_location('published_harness',HERE/'published-tooling/tools/lean/harness.py')
        sys.path.insert(0,str(HERE/'published-tooling/tools/lean'))
        harness=importlib.util.module_from_spec(spec);spec.loader.exec_module(harness)
        (source/'ProofTrustAudit.lean').write_text(harness.proof_trust_source(config))
        targets=', '.join('`'+n for n in config['theorem_names'])
        runner='''import Lean
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
def main : IO Unit := do
  initSearchPath (← findSysroot)
'''
        runner+=f'  let challenge ← imported `{config["challenge_module"]}\n  let solution ← imported `{config["solution_module"]}\n'
        runner+=f'  for name in #[{targets}] do\n'
        runner+='    requireSuccess s!"exact statement and referenced definitions: {name}" <| Comparator.compareAt challenge solution #[name] #[] #[]\n'
        runner+='    requireSuccess s!"transitive standard axioms: {name}" <| Comparator.checkAxioms solution #[name] #[] #[`propext, `Classical.choice, `Quot.sound]\n'
        runner+='  IO.println "All actual support statement/axiom comparisons passed."\n'
        (source/'CompareActual.lean').write_text(runner)
        for _,rel in PINNED:
            run(rel)
        for rel in config['sources']:
            run(rel)
        run('ProofTrustAudit.lean')
        stdout=run('CompareActual.lean',True)
        if 'All actual support statement/axiom comparisons passed.' not in stdout:
            raise RuntimeError('missing completion marker')
        for rel,expected in result['source_sha256'].items():
            if sha(packet/rel)!=expected:
                raise RuntimeError('source changed during review: '+rel)
        result.update(theorem_comparisons=len(config['theorem_names']),comparator_core_executed=True)
        result['pass']=True
    except Exception as error:
        result['error']=str(error)
    finally:
        result['dependencies_after']=dependencies()
        result['snapshot_sha256']={str(p.relative_to(source)):sha(p) for p in source.rglob('*') if p.is_file()}
        shutil.rmtree(build);result['temporary_compiled_objects_removed']=not build.exists()
        (attempt/'result.json').write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps({'attempt':str(attempt),'pass':result['pass'],'error':result.get('error')}),flush=True)
    return 0 if result['pass'] else 1
if __name__=='__main__':
    raise SystemExit(main())
