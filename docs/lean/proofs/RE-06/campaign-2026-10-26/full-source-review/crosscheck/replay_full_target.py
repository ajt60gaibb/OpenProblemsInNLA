#!/usr/bin/env python3
"""Independent exact-181c365 full-target review, continuing only own fresh objects."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
ROOT=Path(__file__).resolve().parent
OUT=ROOT/'full-target';OUT.mkdir(exist_ok=True)
REPO=Path('/Users/ajt253/.codex/worktrees/re06-nonadaptive-oct26/OpenProblemsInNLA')
COMMIT='181c365dc426875aaa61984c901478b1b7c696e6'
LEAN=Path('/private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean')
PACKAGES=Path('/Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(n,d): (OUT/n).write_text(json.dumps(d,indent=2)+'\n')
fpath=REPO/'docs/lean/proofs/RE-06/campaign-2026-10-26/FULL_TARGET_SOURCE_FREEZE.json'
assert sha(fpath)=='93df2eabffe17df3c1d9a2950a60bc0cfcea103e8b4285cbd117b7f945d21e8b'
f=json.loads(fpath.read_text()); full=f['proof_inputs']+f['shared_inputs']; assert len(full)==87
prior=json.loads(Path('/Users/ajt253/Documents/OpenProblemsInNLA/reviews/2026-10-23-solved-lean/re06-outer-moment-author/SOURCE_FREEZE.json').read_text())['files']
fullmap={r['module']:r for r in full}; priormap={r['module']:r for r in prior}
add=[r for r in full if r['module'] not in priormap]
assert len(add)==10 and len(set(priormap)&set(fullmap))==77 and len(set(priormap)-set(fullmap))==5
checks=[]
for r in full:
    p=REPO/r['path']; b=p.read_bytes()
    gitb=subprocess.check_output(['git','-C',str(REPO),'show',f'{COMMIT}:{r["path"]}'])
    assert b==gitb and sha(p)==r['sha256'] and len(b)==r['bytes'],r['path']
    checks.append(dict(path=r['path'],module=r['module'],sha256=r['sha256'],matches_commit=True))
    dest=OUT/'sources'/(r['module'].replace('.','/')+'.lean.txt');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
packet=REPO/'docs/lean/proofs/RE-06/campaign-2026-10-26/preproof'
exports=json.loads((packet/'EXPORTS.json').read_text())
save('SOURCE_CHECKS.json',dict(exact_commit=COMMIT,freeze_sha256=sha(fpath),full87=checks,prior82_sha256='e20c9fba32e1e9b49bdad584d906b85fc206b41b9593b67505d1951f8f9ace85',overlap77=sorted(set(priormap)&set(fullmap)),extra10=[r['module'] for r in add],historical_audits5=sorted(set(priormap)-set(fullmap))))
version=subprocess.check_output([str(LEAN),'--version'],text=True).strip();assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
manifest=json.loads((REPO/'lean-statements/lake-manifest.json').read_text())
def heads():
    h={}
    for p in manifest['packages']:
        h[p['name']]=subprocess.check_output(['git','-C',str(PACKAGES/p['name']),'rev-parse','HEAD'],text=True).strip()
        assert h[p['name']]==p['rev']
    return h
before=heads(); records=[]; captured={};start=time.time()
with tempfile.TemporaryDirectory(prefix='nla-independent-full-target-',dir='/private/tmp') as tmp:
    tmp=Path(tmp);source=tmp/'source';obj=tmp/'objects';source.mkdir();obj.mkdir()
    # The only reused objects come from this reviewer's concurrently running
    # fresh82 replay. Copy each object only after its recorded successful build.
    while len(captured)<82:
        progress=json.loads((ROOT/'PROGRESS.json').read_text())
        for rec in progress['records']:
            mod=rec['module']
            if mod not in priormap or mod in captured: continue
            assert rec['passed'] and rec['exit_code']==0 and rec['source_sha256']==priormap[mod]['sha256'],mod
            old=Path(rec['argv'][rec['argv'].index('-o')+1])
            assert old.is_file(),str(old)
            new=obj/(mod.replace('.','/')+'.olean');new.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(old,new)
            captured[mod]=dict(module=mod,source_sha256=rec['source_sha256'],object_sha256=sha(new),fresh_build_record=rec,old_object_path=str(old))
            save('CAPTURED_FRESH82.json',list(captured.values()))
        if len(captured)<82: time.sleep(1)
    for r in prior+add:
        p=source/(r['module'].replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((REPO/r['path']).read_bytes())
    env=os.environ.copy();env['LEAN_PATH']=':'.join([str(obj)]+[str(p/'.lake/build/lib/lean') for p in sorted(PACKAGES.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]+[str(LEAN.parent.parent/'lib/lean')])
    # Resolve the new ten-module order from their actual imports.
    order=[]
    def visit(mod):
        if mod in captured or mod in order:return
        assert mod in {r['module'] for r in add},mod
        p=source/(mod.replace('.','/')+'.lean')
        for d in re.findall(r'^import\s+([\w.]+)',p.read_text(),re.M):
            if d.startswith(('NLA.','Reviewed.')):visit(d)
        order.append(mod)
    for r in add:visit(r['module'])
    # Independently consume the literal six challenge headers, without
    # rebuilding headers from the author's final-export manifest.
    challenge=(packet/'Challenge.lean').read_text()
    headers=re.findall(r'theorem\s+(\w+)(\s+.*?):= by\n  sorry',challenge,re.S)
    assert [n for n,_ in headers]==['svd_total','query_bound','successful','original_claim','explicit_claim','target']
    params={'svd_total':'','query_bound':' n m hn ε hε0 hεh','successful':' n m hn F hF A ε hε0 hεh','original_claim':'','explicit_claim':'','target':''}
    audit='import NLA.Proofs.RE06.FullTargetAudit\nimport NLA.Proofs.RE06.GaussianMomentOuterAudit\nset_option autoImplicit false\nset_option leancert.trust "kernel"\nnamespace IndependentFullTarget\n'
    for n,h in headers:audit+=f'theorem consume_{n}{h}:= by\n  exact NLA.Proofs.RE06.{n}{params[n]}\n'
    audit+='theorem identity : NLA.Statements.RE06.Target = NLA.ReviewedStatements.RE06.Target := rfl\nend IndependentFullTarget\n'
    for n,_ in headers:
        for name in ['NLA.Proofs.RE06.'+n,'IndependentFullTarget.consume_'+n]:
            audit+=f'#re06_theorem {name}\n#assert_trust kernel {name}\n#print axioms {name}\n'
    for mod in ['GaussianMomentInverseAudit','GaussianMomentOuterAudit']:
        t=(REPO/f'lean-statements/NLA/Proofs/RE06/{mod}.lean').read_text()
        for name in re.findall(r'^#actual_theorem ([\w.]+)',t,re.M):
            audit+=f'#actual_theorem {name}\n#assert_trust kernel {name}\n#print axioms {name}\n'
    holes='import NLA.Proofs.RE06.FullTargetAudit\nset_option leancert.trust "kernel"\nnamespace IndependentHoles\n'
    for n,h in headers:holes+=f'theorem {n}{h}:= by\n  sorry\n'
    for n,_ in headers:holes+=f'#assert_trust kernel {n}\n'
    holes+='end IndependentHoles\n'
    controls={
        'IndependentFull.Audit':audit,
        'IndependentFull.Holes':holes,
        'IndependentFull.Alias':'import NLA.Proofs.RE06.FullTargetAudit\ndef counterfeit := NLA.Proofs.RE06.target\n#re06_theorem counterfeit\n',
        'IndependentFull.Axiom':'import NLA.Proofs.RE06.FullTargetAudit\nset_option leancert.trust "kernel"\naxiom counterfeit : NLA.Statements.RE06.Target\ntheorem forged : NLA.Statements.RE06.Target := counterfeit\n#assert_trust kernel forged\n'}
    for mod,body in controls.items():
        p=source/(mod.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(body)
        dest=OUT/'sources'/(mod.replace('.','/')+'.lean.txt');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(body)
    for mod in order+list(controls):
        src=source/(mod.replace('.','/')+'.lean');dst=obj/(mod.replace('.','/')+'.olean');dst.parent.mkdir(parents=True,exist_ok=True)
        argv=[str(LEAN),'-R',str(source),'-o',str(dst),str(src)]
        p=subprocess.run(argv,cwd=source,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=600);log=p.stdout
        ax=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log);axs=sorted({v.strip() for s in ax for v in s.split(',') if v.strip()})
        reports=len(re.findall(r'(?:depends on axioms:|does not depend on any axioms)',log))
        if mod=='IndependentFull.Holes':ok=p.returncode!=0 and log.count('error: #assert_trust:')==6 and 'sorryAx' in log
        elif mod=='IndependentFull.Alias':ok=p.returncode!=0 and 'expected actual theorem declaration' in log and 'unknown identifier' not in log.lower()
        elif mod=='IndependentFull.Axiom':ok=p.returncode!=0 and 'counterfeit' in log and 'error: #assert_trust:' in log
        else:ok=p.returncode==0 and set(axs)<= {'propext','Classical.choice','Quot.sound'}
        if mod=='IndependentFull.Audit':ok=ok and reports==73
        if mod=='NLA.Proofs.RE06.FullTargetAudit':ok=ok and reports==14
        (OUT/(mod+'.log')).write_text(log)
        records.append(dict(module=mod,argv=argv,source_sha256=sha(src),exit_code=p.returncode,passed=ok,negative=mod in controls and mod!='IndependentFull.Audit',warnings=log.count('warning:'),axioms=axs,axiom_reports=reports))
        save('PROGRESS.json',records);print(f'{len(records)}/14 {mod}: {"PASS" if ok else "FAIL"}',flush=True)
        if not ok:print(log,flush=True);break
after=heads();assert before==after
for r in full:assert sha(REPO/r['path'])==r['sha256']
save('RESULT.json',dict(reviewer='/root/re06_counts/inverse_outer_crosscheck',independent_of_all_source_authors=True,scope='FULL original RE-06 Target source/mathematical review at exact181c365; not Linux CI, Comparator, or canonical-package acceptance',commit=COMMIT,freeze_sha256=sha(fpath),passed=len(records)==14 and all(r['passed'] for r in records),group1_fresh82_record='CAPTURED_FRESH82.json',group2_fresh10=records[:10],own_audit_and_controls=records[10:],unique_project_sources=92,final_import_sources=87,retained_historical_audits=5,source_overlap=77,shared_project_objects_used=False,own_fresh_group_objects_removed=True,lean_version=version,lean_sha256=sha(LEAN),package_heads_before_and_after=before,elapsed_seconds=time.time()-start,records=records))
