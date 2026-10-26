#!/usr/bin/env python3
"""Fresh snapshot author replay of concrete copy/header programs; not TR04 Target."""
import argparse, hashlib, importlib.util, json, os, re, shutil, subprocess
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--tooling',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args()
repo=Path(__file__).resolve().parents[5]
project=repo/'lean-statements'
out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
snapshot=out/'sources';snapshot.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
owned=['MachineScalarBlocks','MachineCopy','MachineHeaderDecode']
targets=['NLA.Proofs.TR04.MachineCopy','NLA.Proofs.TR04.MachineHeaderDecode']
closure={}
def visit(mod):
    if mod in closure:return
    path=Path(mod.replace('.','/')+'.lean')
    src=project/path
    closure[mod]={'path':str(Path('lean-statements')/path),'sha256':sha(src),'bytes':src.stat().st_size}
    dest=snapshot/path;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest)
    for imp in re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',src.read_text(),re.M):
        if imp.startswith(('NLA.','Reviewed.')):visit(imp)
for mod in targets:visit(mod)
for file in ['lean-toolchain','lake-manifest.json','lakefile.toml']:
    shutil.copyfile(project/file,snapshot/file)
(snapshot/'.lake').mkdir();(snapshot/'.lake/packages').symlink_to((project/'.lake/packages').resolve(),target_is_directory=True)
originals=json.loads((repo/'docs/lean/proofs/TR-04/campaign-2026-10-23/input-lock.json').read_text())['records']
for record in originals:assert sha(repo/record['path'])==record['sha256'],record['path']
names=[]
for file in owned:
    text=(snapshot/'NLA/Proofs/TR04'/f'{file}.lean').read_text()
    names += ['NLA.Proofs.TR04.'+name for name in re.findall(r'^(?:@\[[^\]]+\]\s*)?(?:noncomputable\s+)?(?:def|theorem)\s+([A-Za-z0-9_]+)',text,re.M)]
lock={'scope':'Three actual scalar/memory/header program support modules, not a TT solver or full Target','author':'/root','authored_modules':owned,'authored_declarations':names,'targets':targets,'project_closure':list(closure.values()),'reviewed_original_inputs':originals}
(out/'source-lock.json').write_text(json.dumps(lock,indent=2)+'\n')
env=dict(os.environ,NLA_CAMPAIGN_SOURCE_ROOT=str(snapshot),NLA_CAMPAIGN_OBJECT_ROOT=str(out/'objects'))
with (out/'closure.log').open('w') as log:
    r=subprocess.run(['python3',str(a.tooling/'tr06-build-closure.py'),*targets],env=env,stdout=log,stderr=subprocess.STDOUT)
assert r.returncode==0,'closure failed'
consumer='''import NLA.Proofs.TR04.MachineCopy
import NLA.Proofs.TR04.MachineHeaderDecode
set_option leancert.trust "kernel"
open NLA.Computation.SVDMachine NLA.Proofs.TR04
example (mem : ℕ → ℝ) (src dst n : ℕ) (scratch : ℝ)
    (hd : DisjointBlocks src n dst n) (tr : Trace copyProgram)
    (ht : LegalTrace copyProgram (copyLoopState mem src dst n 0 scratch) tr) :
    (tr.state (6*n+2)).status = .halted dst ∧
    (∀ i < n, (tr.state (6*n+2)).memory (dst+i) = mem (src+i)) ∧
    CostThrough copyProgram tr (6*n+2) ≤ 6*n+2 := by
  obtain ⟨hs,hcells,_⟩ := copyProgram_trace_cells mem src dst n scratch hd tr ht
  exact ⟨hs,hcells,copyProgram_trace_cost mem src dst n scratch tr ht⟩
example (mem : ℕ → ℝ) (src dst : ℕ) : copiedMemory mem src dst 0 = mem :=
  copiedMemory_zero mem src dst
example (mem : ℕ → ℝ) (base n : ℕ) (scratch : ℝ) (tr : Trace decodeNaturalProgram)
    (ht : LegalTrace decodeNaturalProgram (decodeNaturalLoopState mem base n 0 scratch) tr) :
    (tr.state (3*n+3)).natural 0 = n ∧ (tr.state (3*n+3)).memory = mem ∧
    (tr.state (3*n+3)).status = .halted base ∧
    CostThrough decodeNaturalProgram tr (3*n+3) ≤ 3*n+3 := by
  have heq := decodeNaturalProgram_trace_result mem base n scratch tr ht
  refine ⟨?_,?_,?_,decodeNaturalProgram_trace_cost mem base n scratch tr ht⟩
  · rw [heq];rfl
  · rw [heq];rfl
  · rw [heq];rfl
example (mem : ℕ → ℝ) (base : ℕ) (scratch : ℝ) :
    (ordinaryStep decodeNaturalProgram)^[3] (decodeNaturalLoopState mem base 0 0 scratch) =
      decodeNaturalFinalState mem base 0 := decodeNaturalProgram_exit mem base 0 scratch
'''
for name in names:consumer+=f'#assert_trust kernel {name}\n#print axioms {name}\n'
cp=out/'ScalarProgramsConsumer.lean.txt';cp.write_text(consumer)
spec=importlib.util.spec_from_file_location('pinned_lean',a.tooling/'tr06-lean.py');m=importlib.util.module_from_spec(spec)
os.environ.update(NLA_CAMPAIGN_SOURCE_ROOT=str(snapshot),NLA_CAMPAIGN_OBJECT_ROOT=str(out/'objects'));spec.loader.exec_module(m)
with (out/'consumer.log').open('w') as log:
    r=subprocess.run([str(m.BIN/'lean'),str(cp)],cwd=snapshot,env=m.ENV,stdout=log,stderr=subprocess.STDOUT)
assert r.returncode==0,'consumer failed'
for rec in closure.values():assert sha(repo/rec['path'])==rec['sha256'],rec['path']
for rec in originals:assert sha(repo/rec['path'])==rec['sha256'],rec['path']
manifest=json.loads((project/'lake-manifest.json').read_text())
pins=[]
for pkg in manifest['packages']:
    path=(project/'.lake/packages'/pkg['name']).resolve()
    head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=path,text=True).strip()
    dirty=subprocess.check_output(['git','status','--porcelain','--untracked-files=normal'],cwd=path,text=True)
    assert head==pkg['rev'] and not dirty,pkg['name']
    pins.append({'name':pkg['name'],'revision':head,'clean':True})
commands=sum(line.endswith(' 0') for line in (out/'closure.log').read_text().splitlines())+1
assert commands==len(closure)+1
report={'passed':True,'scope':lock['scope'],'author':'/root','new_modules':3,'project_modules_rebuilt':len(closure),'successful_commands':commands,'public_declaration_kernel_checks':len(names),'literal_consumer_examples':4,'project_objects_reused':False,'pinned_external_objects_reused':True,'pinned_dependencies':pins,'source_lock_sha256':sha(out/'source-lock.json'),'consumer_sha256':sha(cp),'reviewed_original_inputs_unchanged':len(originals),'logs':{p.name:sha(p) for p in out.glob('*.log')}}
(out/'result.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
