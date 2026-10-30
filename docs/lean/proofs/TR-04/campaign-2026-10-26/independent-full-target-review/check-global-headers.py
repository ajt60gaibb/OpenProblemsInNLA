#!/usr/bin/env python3
"""Fresh test of complete original global-name theorem-header generation."""
from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,os,re,subprocess,tempfile
from source_inventory import declarations_of,without_comments
B=Path(__file__).resolve().parent;REPO=B.parents[5]
LEAN=REPO.parent/'tooling/lean-4.33.1-darwin_aarch64/bin/lean'
PACKAGES=(REPO/'tensor-computations/TR-04/lean/.lake/packages').resolve()
sha=lambda b:hashlib.sha256(b).hexdigest()
text=(B/'replay.py').read_text();tree=ast.parse(text)
literal=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='literal')
preamble=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='preamble' for t in n.targets))
raw=(REPO/'tensor-computations/TR-04/lean/Solution.lean').read_bytes()
assert sha(raw)=='dd02b5ba519b14e19aeebd005a72c85aba30084347bc3e82d5d8f61d4a94aa75'
decls=declarations_of('Solution.lean',raw);assert len(decls)==2
env={'lookup':{d['name']:d for d in decls},'frozen':{'Solution.lean':raw},'without_comments':without_comments,'re':re,'sha':sha}
exec(compile(ast.Module(body=[literal],type_ignores=[]),'<global-header-fixture>','exec'),env)
consumer='import GlobalOriginal\nimport LeanCert.Tactic.Verification\n'+preamble+'\nnoncomputable section\n'
records=[]
for d in decls:
    assert d['visibility']=='public' and d['kind']=='theorem'
    consumer+=f'#audit_named "{d["name"]}" "GlobalOriginal" "public" "theorem"\n'
    code,r=env['literal'](d['name']);consumer+=code;records.append(r)
consumer+='end\n'
out=B/'global-header-controls';out.mkdir(exist_ok=False)
(out/'GlobalOriginal.lean').write_bytes(raw);(out/'GlobalConsumer.lean').write_text(consumer)
commands=[]
with tempfile.TemporaryDirectory(prefix='objects-',dir=B) as tmp:
    libs=[p/'.lake/build/lib/lean' for p in sorted(PACKAGES.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]
    shellenv=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[Path(tmp),*libs,LEAN.parent.parent/'lib/lean'])))
    for name in ['GlobalOriginal.lean','GlobalConsumer.lean']:
        p=subprocess.run([str(LEAN),'-R',str(out),'-o',str(Path(tmp)/Path(name).with_suffix('.olean')),str(out/name)],cwd=out,env=shellenv,text=True,capture_output=True)
        log=p.stdout+p.stderr;(out/(name+'.log')).write_text(log)
        commands.append({'source':name,'source_sha256':sha((out/name).read_bytes()),'exit_code':p.returncode,'log_sha256':sha(log.encode())})
        assert p.returncode==0,log
log=(out/'GlobalConsumer.lean.log').read_text()
assert sorted(re.findall(r'AUDITED_KIND (\S+) theorem',log))==sorted(d['name'] for d in decls)
assert sorted(re.findall(r'AUDITED_AXIOMS (\S+) \[\]',log))==sorted(d['name'] for d in decls)
result={'passed':True,'executed_utc':datetime.now(timezone.utc).isoformat(),'driver_sha256':sha(text.encode()),
 'checker_sha256':sha(Path(__file__).read_bytes()),'scope':'Global original theorem names and full raw binder/type applications only; no complete canonical or Target acceptance.',
 'fresh_commands':2,'project_objects_reused':False,'literal_headers':records,'commands':commands,'proof_source_changes':False}
(out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':True,'sha256':sha((out/'result.json').read_bytes())}))
