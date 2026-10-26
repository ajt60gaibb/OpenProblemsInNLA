#!/usr/bin/env python3
"""Independent non-author IE22 frozen-input and pre-proof evidence audit."""
import hashlib,json,os,subprocess
from pathlib import Path
PACKET=Path(__file__).resolve().parent
REPO=PACKET.parents[2]
BUILD=Path('/private/tmp/nla-ie22-verification-preproof-fresh')
LEAN=Path('/private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean')
PKG=Path('/Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages')
OUT=PACKET/'verification'/'verification-preproof'
OUT.mkdir(parents=True,exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
lock=json.loads((PACKET/'INPUT_LOCK.json').read_text())
checks=[]
for item in lock['reviewed_inputs']:
    data=(PACKET/'frozen'/item['path']).read_bytes()
    published=subprocess.check_output(['git','show',lock['published_base']+':'+item['path']],cwd=REPO)
    checks.append(dict(path=item['path'],passed=data==published and len(data)==item['bytes'] and sha(data)==item['sha256'],sha256=sha(data)))
hashes={n:sha((PACKET/n).read_bytes()) for n in ['CONTRACT.md','Challenge.lean','INPUT_LOCK.json','check_scaffold.py']}
assert all(hashes[n]==h for n,h in lock['packet_files'].items())
scaffold=json.loads((BUILD/'result.json').read_text())
assert scaffold['passed'] and len(scaffold['commands'])==4
assert (BUILD/'logs/Challenge.log').read_text().count('warning: declaration uses `sorry`')==3
deps=sorted(p/'.lake/build/lib/lean' for p in PKG.iterdir() if (p/'.lake/build/lib/lean').is_dir())
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[BUILD/'out']+deps+[LEAN.parent.parent/'lib/lean']))
commands=[]
def compile_extra(name,text,obj=False):
    path=BUILD/'source'/(name.replace('.','/')+'.lean');path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
    argv=[str(LEAN),'-R',str(BUILD/'source')]
    if obj:
        op=BUILD/'out'/(name.replace('.','/')+'.olean');op.parent.mkdir(parents=True,exist_ok=True);argv+=['-o',str(op)]
    argv+=[str(path)]
    p=subprocess.run(argv,cwd=BUILD/'source',env=env,capture_output=True,text=True,timeout=120)
    log=p.stdout+p.stderr;(OUT/(name+'.log')).write_text(log);(OUT/(name+'.lean.txt')).write_text(text)
    commands.append(dict(module=name,argv=argv,exit_code=p.returncode,source_sha256=sha(text.encode()),log_sha256=sha(log.encode())))
    return p.returncode,log
code=(PACKET/'frozen/lean-statements/Reviewed/IE22.lean').read_text()
assert compile_extra('Reviewed.IE22',code,True)[0]==0
equiv='import Reviewed.IE22\nimport NLA.Statements.IE22\nexample : NLA.ReviewedStatements.IE22.Target ↔ NLA.Statements.IE22.Target := Iff.rfl\n'
assert compile_extra('VerificationBoundaryEquivalence',equiv)[0]==0
names=['uniform_squared_upper','near_sharp_unit_row_witness','target']
negative='import Challenge\nset_option leancert.trust "kernel"\n'+''.join('#assert_trust kernel NLA.Proofs.IE22.'+n+'\n' for n in names)
exit_code,log=compile_extra('VerificationPlaceholderRejection',negative)
rejected=exit_code!=0 and log.count('sorryAx')>=3 and all('NLA.Proofs.IE22.'+n in log for n in names)
pins=[]
for pin in json.loads((PACKET/'frozen/linear-systems-and-elimination/IE-22/lean/lake-manifest.json').read_text())['packages']:
    path=PKG/pin['name'];head=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD']).decode().strip()
    clean=not subprocess.check_output(['git','-C',str(path),'status','--porcelain','--untracked-files=no'])
    pins.append(dict(name=pin['name'],expected=pin['rev'],actual=head,tracked_clean=clean,passed=head==pin['rev'] and clean))
for p in (BUILD/'logs').iterdir():(OUT/p.name).write_bytes(p.read_bytes())
(OUT/'scaffold-result.json').write_bytes((BUILD/'result.json').read_bytes())
report=dict(reviewer='/root/verification',authored_IE22_proof_sources=[],date='2026-10-23',verdict='APPROVE frozen exact three signatures and mathematical route; no changes requested',scope='Independent non-author pre-proof review; no mathematical endpoint is proved',published_base=lock['published_base'],packet_hashes=hashes,input_checks=checks,dependency_pins=pins,compiler_version=subprocess.check_output([str(LEAN),'--version']).decode().strip(),compiler_sha256=sha(LEAN.read_bytes()),scaffold=scaffold,additional_commands=commands,all_three_placeholders_rejected_with_sorryAx=rejected,reviewed_target_definitionally_equivalent=True,passed=all(c['passed'] for c in checks) and all(c['passed'] for c in pins) and rejected and scaffold['passed'])
(PACKET/'PRE_REVIEW_VERIFICATION.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(passed=report['passed'],frozen_inputs=len(checks),scaffold_commands=len(scaffold['commands']),additional_positive_commands=2,placeholders_rejected=3 if rejected else 0,pins=len(pins))))
raise SystemExit(0 if report['passed'] else 1)
