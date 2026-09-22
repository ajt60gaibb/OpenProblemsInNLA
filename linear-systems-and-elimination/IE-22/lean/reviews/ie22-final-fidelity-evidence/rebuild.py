import pathlib,json,hashlib,subprocess,os,tempfile,re,datetime,time
p=pathlib.Path.cwd(); e=p/'reviews/ie22-final-fidelity-evidence'; out=pathlib.Path(tempfile.mkdtemp(prefix='nla-ie22-fidelity-fresh-')); lean=pathlib.Path('/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean'); cache=pathlib.Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages')
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
freeze=json.loads((p/'reviews/package-source-freeze.json').read_text())['source_sha256']; before={f:sha(p/f) for f in freeze}; assert before==freeze
(e/'hashes-before.json').write_text(json.dumps(before,indent=2)+'\n')
sources={str(q.relative_to(p)):q for q in sorted((p/'NLA').rglob('*.lean'))}; order=[]; done=set()
def visit(f):
 if f in done:return
 for mod in re.findall(r'^import\s+(NLA[\w.]*)',sources[f].read_text(),re.M):
  child=mod.replace('.','/')+'.lean'; assert child in sources;visit(child)
 done.add(f);order.append(f)
for f in sources:visit(f)
assert len(order)==47
cachepaths=sorted(q for q in cache.glob('*/.lake/build/lib/lean') if q.is_dir()); env=os.environ.copy(); env['LEAN_PATH']=':'.join(map(str,[out,*cachepaths])); entries=[]; start=datetime.datetime.now(datetime.timezone.utc).isoformat()
for i,f in enumerate(order):
 dst=out/pathlib.Path(f).with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True)
 cmd=[str(lean),'-o',str(dst),f];t=time.monotonic();r=subprocess.run(cmd,cwd=p,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 log=e/(f.replace('/','__')+'.log');log.write_text(r.stdout)
 entries.append({'source':f,'command':cmd,'exit_code':r.returncode,'seconds':round(time.monotonic()-t,3),'log':str(log.relative_to(p)),'log_sha256':sha(log)})
 print(f'{i+1}/47 {f}: {r.returncode}',flush=True)
 (e/'build-progress.json').write_text(json.dumps({'build_directory':str(out),'lean_path':env['LEAN_PATH'],'steps':entries},indent=2)+'\n')
 if r.returncode:raise SystemExit(r.stdout)
text=(p/'Challenge.lean').read_text();names=json.loads((p/'comparator.json').read_text())['theorem_names'];text=text.replace('import NLA.IE22.Definitions','import NLA.IE22.Final')
for name in names:
 short=name.rsplit('.',1)[1]; pat=r'(?m)^theorem '+re.escape(short)+r'\b([\s\S]*?) := by sorry'
 text,n=re.subn(pat,lambda m:'example'+m.group(1)+' := '+name+'\n#print axioms '+name,text,count=1);assert n==1,name
assert 'by sorry' not in text
# Historical header removed; signatures retained literally, no Challenge declarations imported.
text=re.sub(r'/\-![\s\S]*?\-/','/- Independent exact full signature and axiom audit; generated from frozen Challenge bytes. -/',text,count=1)
audit=e/'ExactTypesAndAxioms.lean';audit.write_text(text); cmd=[str(lean),str(audit.relative_to(p))];r=subprocess.run(cmd,cwd=p,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(e/'exact-types-and-axioms.log').write_text(r.stdout)
print(r.stdout,flush=True);assert r.returncode==0
found=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",r.stdout);assert len(found)==20;assert [n for n,_ in found]==names
allowed={'propext','Classical.choice','Quot.sound'};assert all({x.strip() for x in ax.split(',')}==allowed for _,ax in found)
after={f:sha(p/f) for f in freeze};assert after==before
receipt={'reviewer':'ie22_final_fidelity','independent_nonauthor':True,'started_utc':start,'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'build_directory':str(out),'compiler':str(lean),'compiler_version':subprocess.check_output([str(lean),'--version'],text=True).strip(),'project_modules_rebuilt':47,'reused_project_objects':0,'dependency_cache':str(cache),'lean_path':env['LEAN_PATH'],'source_sha256_before':before,'source_sha256_after':after,'steps':entries,'exact_frozen_full_signatures_checked':20,'signature_audit_sha256':sha(audit),'transitive_axioms':{n:[x.strip() for x in ax.split(',')] for n,ax in found},'audit_log_sha256':sha(e/'exact-types-and-axioms.log'),'limitations':['Local Darwin arm64 compilation with cached upstream dependency objects, not an authentic Linux Comparator or LeanCert wrapper run.']}
(e/'build-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print('INDEPENDENT_BUILD_PASS',flush=True)
