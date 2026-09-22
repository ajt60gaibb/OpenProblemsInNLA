#!/usr/bin/env python3
"""Author milestone only: fresh local modules, cached pinned dependencies."""
from pathlib import Path
import hashlib,json,os,re,subprocess,tempfile
root=Path(__file__).resolve().parents[2]
evidence=Path(__file__).resolve().parent
build=Path(tempfile.mkdtemp(prefix='nla-ie21-spherical-trimming-milestone-'))
packages=Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages')
lean=Path('/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean')
env=os.environ.copy()
env['LEAN_PATH']=os.pathsep.join([str(build),str(root)]+[
 str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if p.is_dir()])
files=['NLA/IE21/Definitions.lean','NLA/IE21/GaussianTrimming.lean','NLA/IE21/PopulationTrimming.lean','NLA/IE21/SphericalLaw.lean','NLA/IE21/GaussianPolar.lean','NLA/IE21/GaussianMoments.lean','NLA/IE21/SphericalMoments.lean','NLA/IE21/SphericalTrimming.lean','reviews/gaussian-trimming-author-evidence/SphericalTrimmingAxioms.lean']
records=[]
with (evidence/'spherical-trimming-typecheck.log').open('w') as log:
 log.write('Author macOS milestone build; cached pinned dependencies. No Comparator or full verification claim.\n')
 log.write(subprocess.check_output([str(lean),'--version'],text=True))
 for file in files:
  source=root/file
  digest=hashlib.sha256(source.read_bytes()).hexdigest()
  output=build/Path(file).with_suffix('.olean');output.parent.mkdir(parents=True,exist_ok=True)
  cmd=[str(lean),'-o',str(output),file]
  log.write('SOURCE SHA256: '+digest+'\nCOMMAND: '+json.dumps(cmd)+'\n');log.flush()
  result=subprocess.run(cmd,cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  log.write(result.stdout+'EXIT: '+str(result.returncode)+'\n');log.flush()
  print(file,result.returncode,result.stdout,flush=True)
  records.append({'path':file,'sha256':digest,'exit':result.returncode})
  if result.returncode:raise SystemExit(result.returncode)
assert all(hashlib.sha256((root/r['path']).read_bytes()).hexdigest()==r['sha256'] for r in records)
log_text=(evidence/'spherical-trimming-typecheck.log').read_text()
axioms=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log_text)
assert len(axioms)==4,axioms
allowed={'propext','Classical.choice','Quot.sound'}
assert all(set(a.strip() for a in closure.split(','))<=allowed for _,closure in axioms)
receipt={'milestone':'exact spherical-to-Gaussian population trimming bound',
 'scope':'one exact frozen IE-21 target spherical_gaussian_trimming plus three helpers; remaining campaign gates not run',
 'author_agent':'reference_review','independent_final_review':False,
 'complete_verification':False,'comparator_executed':False,'leancert_executed':False,
 'output_directory':str(build),'files':records,
 'public_axiom_closures':{name:[a.strip() for a in closure.split(',')] for name,closure in axioms},
 'log_sha256':hashlib.sha256((evidence/'spherical-trimming-typecheck.log').read_bytes()).hexdigest()}
(evidence/'spherical-trimming-author-evidence.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('Evidence saved; 4 public axiom closures allowed. Build:',build,flush=True)
