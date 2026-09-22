from pathlib import Path
import os, subprocess, sys, hashlib, json, re, datetime
root=Path(__file__).resolve().parents[2]
evidence=Path(__file__).resolve().parent
build=Path('/private/tmp/nla-ie21-trimming-referee-infrastructure-build')
if build.exists(): raise SystemExit('Fresh build directory already exists; refusing reuse')
build.mkdir()
lean=Path('/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean')
packages=Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages')
targets=['QuantileTrimming','EmpiricalTrimming','UniformTrimmingGeometry','UniformTrimmingBound','FiniteSizeGeometry','AsymptoticTail']
expected={'QuantileTrimming':'c1601c196a8c6c08f187ee0b6eb699ea1781b34ab0a639c0e1e6bd3da09eb098','EmpiricalTrimming':'3e634d650b5f7d066457d9eccd8406ae0945c1774890282b2a5ac8cf58000267','UniformTrimmingGeometry':'4c6d0f86d75d29d71b20ba0ae24716e16ebf0b78aedef6aabb4a05ac3b6cd986','UniformTrimmingBound':'e1eebfad4467353c09844da9a39b466650befa14c79a3d445f1febc747b07267','FiniteSizeGeometry':'0ac88a9e6b40f0ac7b85c5f698ee54c92d7ce86199b61202fb84d060c502efa7'}
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
ordered=[]
seen=set()
def visit(path):
    if path in seen: return
    seen.add(path)
    for imp in re.findall(r'^import (NLA\.IE21\.\w+)', (root/path).read_text(), re.M): visit(imp.replace('.', '/')+'.lean')
    ordered.append(path)
for name in targets: visit('NLA/IE21/'+name+'.lean')
sources={p:sha(root/p) for p in ordered}
for name, value in expected.items(): assert sources['NLA/IE21/'+name+'.lean']==value, name
names=[]
for name in targets:
    text=(root/('NLA/IE21/'+name+'.lean')).read_text()
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b|^import Challenge',text,re.M), name
    names.extend('NLA.IE21.'+n for n in re.findall(r'^(?:theorem|lemma|def) (\w+)',text,re.M))
audit=''.join('import NLA.IE21.'+name+'\n' for name in targets)+'\n'+''.join('#print axioms '+name+'\n' for name in names)
(evidence/'Axioms.lean').write_text(audit)
env=os.environ.copy()
env['LEAN_PATH']=os.pathsep.join([str(build),str(root)]+[str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if p.is_dir()])
commands=[]
with (evidence/'typecheck.log').open('w') as log:
    log.write('Independent module-only review build by Codex AI /root/infrastructure_audit; macOS cached dependencies. No Linux Comparator/LeanCert completion claim.\n')
    log.write(subprocess.check_output([str(lean),'--version'],text=True))
    for path in ordered+['reviews/trimming-referee-infrastructure-evidence/Axioms.lean']:
        out=build/Path(path).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
        cmd=[str(lean),'-o',str(out),path]
        log.write('COMMAND: '+' '.join(cmd)+'\n');log.flush()
        p=subprocess.run(cmd,cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        log.write(p.stdout+'EXIT: '+str(p.returncode)+'\n');log.flush()
        commands.append({'argv':cmd,'exit':p.returncode})
        print(path,p.returncode,flush=True)
        if p.returncode: raise SystemExit(p.returncode)
for path,value in sources.items(): assert sha(root/path)==value, 'Source changed during build: '+path
log=(evidence/'typecheck.log').read_text()
assert 'warning:' not in log and 'error:' not in log
closures={}
for name in names:
    match=re.search("'"+re.escape(name)+"' depends on axioms: \[([^]]*)\]",log)
    assert match,name
    values=[x.strip() for x in match.group(1).split(',')]
    assert set(values)<=set(['propext','Classical.choice','Quot.sound']), (name,values)
    closures[name]=values
receipt={'reviewer':'Codex AI /root/infrastructure_audit','timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'verdict':'APPROVE, module-only review','independent_of_reviewed_module_authorship':True,'authorship_disclosure':'Reviewer authored SphericalLaw and RowLaw among rebuilt dependencies, plus GaussianPolar, GaussianMoments, SphericalMoments and SphericalMGF outside this build; this is not a full-package independent review.','reviewed_modules':['NLA/IE21/'+n+'.lean' for n in targets],'source_sha256':sources,'author_receipt_hash_matches':expected,'external_fresh_build':str(build),'commands':commands,'axiom_closures':closures,'complete_problem_verification':False,'comparator_executed':False,'leancert_executed':False,'evidence_sha256':{name:sha(evidence/name) for name in ['build.py','Axioms.lean','typecheck.log']}}
(evidence/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS: fresh rebuild, all source hashes stable, '+str(len(names))+' permitted axiom closures',flush=True)
