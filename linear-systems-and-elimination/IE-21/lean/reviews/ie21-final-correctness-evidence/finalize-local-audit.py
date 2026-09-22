from pathlib import Path
import os,re,json,hashlib,subprocess,datetime
r=Path('/private/tmp/nla-solved-campaign-20260922/docs/lean/campaign/2026-09-22/IE-21/lean');e=r/'reviews/ie21-final-correctness-evidence';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
log=(e/'typecheck.log').read_text();(e/'initial-typecheck-with-linter-warnings.log').write_text(log)
audit=e/'ExactTypesAndAxioms.lean';s=audit.read_text();s=s.replace('set_option autoImplicit false\n','set_option autoImplicit false\nset_option linter.unusedVariables false\n');audit.write_text(s)
records=[]
for cmd,output,ret in re.findall(r'COMMAND ([^\n]+)\n([\s\S]*?)EXIT (\d+)\n',log):
 records.append({'command':json.loads(cmd),'exit_code':int(ret),'output':output})
assert len(records)==32
assert all(x['exit_code']==0 for x in records)
assert all(not re.search(r'\b(?:error|warning):',x['output']) for x in records[:-1])
old=records[-1]['output'];assert not re.search(r'\berror:',old)
assert all('Variable name' in x for x in re.findall(r'warning: ([^\n]+)',old))
inputs=json.loads((e/'initial-input-hashes.json').read_text());assert all(sha(r/k)==v for k,v in inputs.items())
first=records[0]['command'];out=Path(first[first.index('-o')+1]).parents[2]
cache=Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages');env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,[out,r]+sorted(cache.glob('*/.lake/build/lib/lean'))))
x=subprocess.run(records[-1]['command'],cwd=r,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);print(x.stdout);assert x.returncode==0 and not re.search(r'\b(?:error|warning):',x.stdout)
records[-1]={'command':records[-1]['command'],'exit_code':x.returncode,'output':x.stdout}
newlog=log.split('COMMAND ')[0]+''.join('COMMAND '+json.dumps(x['command'])+'\n'+x['output']+'EXIT '+str(x['exit_code'])+'\n' for x in records);(e/'typecheck.log').write_text(newlog)
config=json.loads((r/'comparator.json').read_text());closures={n:[v.strip() for v in a.split(',')] for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",x.stdout)}
assert set(closures)==set(config['theorem_names']);assert all(set(v)==set(config['permitted_axioms']) for v in closures.values())
record={'reviewer':'Codex AI independent nonauthor correctness referee /root/ie21_final_correctness','timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'result':'PASS independently rebuilt all 31 source modules, 23 exact frozen types and permitted axiom closures','build_directory':str(out),'module_count':31,'source_hashes':inputs,'selected_axiom_closures':closures,'command_results':records,'toolchain_version':log.splitlines()[0],'audit_warning_resolution':'All source compiles had zero warnings. First reviewer-only exact-type audit compiled successfully with unused-binder linter warnings; retained initial log. Disabled only that linter in reviewer-only audit, reran the audit against unchanged independently built outputs, and observed zero warnings/errors. No project source changed.','evidence_sha256':{p.name:sha(p) for p in [e/'rebuild.py',audit,e/'typecheck.log',e/'initial-typecheck-with-linter-warnings.log']},'limits':['Shared cached pinned dependency artifacts, independently rebuilt project outputs; not fresh dependency authentication.','Authentic Linux LeanCert and Comparator gates still pending.','AI agent review, not human peer review or official Tau Ceti endorsement.']}
(e/'rebuild-receipt.json').write_text(json.dumps(record,indent=2)+'\n')
(e/'audit-warning-resolution.md').write_text('The initial independent build successfully compiled all 31 source modules and the 23 exact-type examples. Its strict runner then stopped on unused-binder warnings in the reviewer-generated examples. No proof source emitted a warning or error. The original log is retained. The reviewer disabled only `linter.unusedVariables` in its own exact-type file and reran that file against the unchanged reviewer-only fresh build, obtaining zero warnings/errors and the same 23 permitted axiom closures. The final consolidated log combines the actual original proof compile commands with this actual successful audit rerun.\n')
print('PASS',out)
