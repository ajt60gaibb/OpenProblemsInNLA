#!/usr/bin/env python3
"""Compile/import pinned trust API only; no new certificate or TR-06 proof."""
from pathlib import Path
import os,subprocess,json,hashlib,sys
root=Path('/private/tmp/tr06-leancert')
evidence=Path('/private/tmp/tr06-infra/leancert')
compiler=Path('/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.tools/lean-4.33.1-darwin_aarch64/bin/lean')
packages=Path('/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.lake/packages')
expected='621a43d7cf21f87872392a01e874f2f1dbddc926'
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
assert head==expected,(head,expected)
assert subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=root,text=True)==''
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
tracked=subprocess.check_output(['git','ls-files','-z'],cwd=root).decode().rstrip('\0').split('\0')
sources={p:sha(root/p) for p in tracked if (root/p).is_file()}
(evidence/'source-hashes.json').write_text(json.dumps(sources,indent=2)+'\n')
build=root/'.lake/build/lib/lean';target=build/'LeanCert/Tactic/Verification.olean';target.parent.mkdir(parents=True,exist_ok=True)
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(build),*(str(p/'.lake/build/lib/lean') for p in packages.iterdir() if (p/'.lake/build/lib/lean').exists())])
commands=[('build-verification',[str(compiler),'-o',str(target),'LeanCert/Tactic/Verification.lean']),('trust-api',[str(compiler),str(evidence/'TrustAPIProbe.lean')])]
report={'scope':'Development trust API import and existing Mathlib theorem axiom check only; no new theorem, certificate, TR-06 verification or Linux Comparator execution.','leancert_commit':head,'leancert_source':str(root),'source_manifest_sha256':sha(evidence/'source-hashes.json'),'lean_version':subprocess.check_output([str(compiler),'--version'],text=True).strip(),'lean_path':env['LEAN_PATH'],'runs':[]}
failed=False
for name,command in commands:
 r=subprocess.run(command,cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 log=evidence/(name+'.log');log.write_text(r.stdout)
 report['runs'].append({'name':name,'command':command,'cwd':str(root),'exit':r.returncode,'log':log.name,'log_sha256':sha(log)})
 failed|=r.returncode!=0
 print(name, r.returncode);print(r.stdout)
 if failed:break
report['source_unchanged']=all(sha(root/p)==h for p,h in sources.items());report['passed']=not failed and report['source_unchanged'];report['probe_sha256']=sha(evidence/'TrustAPIProbe.lean')
(evidence/'results.json').write_text(json.dumps(report,indent=2)+'\n');sys.exit(not report['passed'])
