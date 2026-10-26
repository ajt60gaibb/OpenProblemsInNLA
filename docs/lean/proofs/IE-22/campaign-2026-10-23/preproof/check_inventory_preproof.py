#!/usr/bin/env python3
"""Independent frozen-byte review bindings and explicit placeholder rejection."""
from pathlib import Path
import hashlib
import json
import os
import subprocess

ROOT=Path('/Users/ajt253/Documents/OpenProblemsInNLA')
PACKET=Path(__file__).resolve().parent
BUILD=Path('/private/tmp/nla-ie22-inventory-preproof-oct23')
LEAN=Path('/private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean')
PKG=Path('/Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages')
OUT=PACKET/'verification'/'inventory-preproof'
OUT.mkdir(parents=True,exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
lock=json.loads((PACKET/'INPUT_LOCK.json').read_text())
checks=[]
for x in lock['reviewed_inputs']:
    b=(PACKET/'frozen'/x['path']).read_bytes()
    published=subprocess.check_output(['git','show',lock['published_base']+':'+x['path']],cwd=ROOT)
    checks.append(dict(path=x['path'],passed=b==published and sha(b)==x['sha256'] and len(b)==x['bytes'],sha256=sha(b)))
packet_hashes={n:sha((PACKET/n).read_bytes()) for n in ['Challenge.lean','CONTRACT.md','INPUT_LOCK.json','check_scaffold.py']}
for n,h in lock['packet_files'].items():
    assert packet_hashes[n]==h,n
scaffold=json.loads((BUILD/'result.json').read_text())
assert scaffold['passed'] and len(scaffold['commands'])==4
assert (BUILD/'logs/Challenge.log').read_text().count('warning: declaration uses `sorry`')==3
names=['uniform_squared_upper','near_sharp_unit_row_witness','target']
control='import Challenge\nset_option leancert.trust "kernel"\n'+''.join('#assert_trust kernel NLA.Proofs.IE22.'+n+'\n' for n in names)
controlpath=BUILD/'source/InventoryPlaceholderRejection.lean'
controlpath.write_text(control)
env=os.environ.copy()
deps=sorted(p/'.lake/build/lib/lean' for p in PKG.iterdir() if (p/'.lake/build/lib/lean').is_dir())
env['LEAN_PATH']=':'.join(map(str,[BUILD/'out']+deps+[LEAN.parent.parent/'lib/lean']))
argv=[str(LEAN),'-R',str(BUILD/'source'),str(controlpath)]
p=subprocess.run(argv,cwd=BUILD/'source',env=env,capture_output=True,text=True,timeout=120)
log=p.stdout+p.stderr
(OUT/'InventoryPlaceholderRejection.lean.txt').write_text(control)
(OUT/'placeholder-rejection.log').write_text(log)
rejected=p.returncode!=0 and all('NLA.Proofs.IE22.'+n in log for n in names) and log.count('sorryAx')>=3
pinpath=PACKET/'frozen/linear-systems-and-elimination/IE-22/lean/lake-manifest.json'
pins=[]
for pin in json.loads(pinpath.read_text())['packages']:
    directory=PKG/pin['name']
    head=subprocess.check_output(['git','-C',str(directory),'rev-parse','HEAD']).decode().strip()
    dirty=subprocess.check_output(['git','-C',str(directory),'status','--porcelain','--untracked-files=no']).decode()
    pins.append(dict(name=pin['name'],expected=pin['rev'],actual=head,tracked_clean=not dirty,passed=head==pin['rev'] and not dirty))
version=subprocess.check_output([str(LEAN),'--version']).decode().strip()
result=dict(reviewer='/root/inventory',authored_IE22_proof_sources=[],date='2026-10-23',verdict='APPROVE frozen exact three signatures and mathematical route; no changes requested',
    scope='Pre-proof source/route review, fresh four-module typecheck and intentional-hole rejection; no implementation or Linux/Comparator acceptance',
    published_base=lock['published_base'],packet_hashes=packet_hashes,input_checks=checks,compiler_version=version,
    compiler_binary_sha256=sha(LEAN.read_bytes()),dependency_pins=pins,scaffold=scaffold,
    negative_control=dict(argv=argv,exit_code=p.returncode,all_three_placeholders_rejected_with_sorryAx=rejected,source_sha256=sha(control.encode()),log_sha256=sha(log.encode())),
    passed=all(x['passed'] for x in checks) and all(x['passed'] for x in pins) and scaffold['passed'] and rejected)
for x in (BUILD/'logs').iterdir():
    (OUT/x.name).write_bytes(x.read_bytes())
(OUT/'scaffold-result.json').write_bytes((BUILD/'result.json').read_bytes())
(PACKET/'PRE_REVIEW_INVENTORY.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(passed=result['passed'],frozen_inputs=len(checks),fresh_positive_commands=len(scaffold['commands']),all_three_holes_rejected=rejected,dependency_pins=len(pins)),indent=2))
if not result['passed']:
    print(log)
    raise SystemExit(1)
