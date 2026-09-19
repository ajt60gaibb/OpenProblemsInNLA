from pathlib import Path
import datetime, hashlib, json, re
ROOT=Path(__file__).resolve().parents[2]
BASE=ROOT/'development/PF03-agent-packaging-v1'
P=BASE/'project'
OUT=Path(__file__).resolve().parent
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def strip_lean(s):
    # Strip nested comments and quoted strings without interpreting any source.
    out=[];i=0;depth=0
    while i<len(s):
        if depth:
            if s.startswith('/-',i):depth+=1;i+=2
            elif s.startswith('-/',i):depth-=1;i+=2
            else:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif s.startswith('/-',i):depth=1;out.append(' ');i+=2
        elif s.startswith('--',i):
            e=s.find('\n',i);i=len(s) if e<0 else e
        elif s[i]=='"':
            out.append(' ');i+=1
            while i<len(s):
                if s[i]=='\\':i+=2
                elif s[i]=='"':i+=1;break
                else:i+=1
        else:out.append(s[i]);i+=1
    assert depth==0
    return ''.join(out)
manifest=json.loads((BASE/'STAGING-HANDOFF.json').read_text())
assert sha(BASE/'STAGING-HANDOFF.json')=='b282175f2f9ad97cf324280013ee3c880477ca5bbaeb4b6a3dfdc112df57829c'
mismatches=[f for f,d in manifest['project_files'].items() if not (P/f).is_file() or sha(P/f)!=d['sha256']]
assert not mismatches,mismatches
sources={p.relative_to(P).as_posix():p.read_text() for p in P.rglob('*.lean')}
code={f:strip_lean(s) for f,s in sources.items()}
modules={f[:-5].replace('/','.'):f for f in sources}
imports={m:re.findall(r'^import\s+(\S+)',code[f],re.M) for m,f in modules.items()}
seen=set();stack=set();external=set()
def visit(m):
    if m in stack:raise AssertionError(('cycle',m))
    if m in seen:return
    if m not in modules:external.add(m);return
    stack.add(m)
    for q in imports[m]:visit(q)
    stack.remove(m);seen.add(m)
visit('Solution')
assert 'Challenge' not in seen
assert len(seen)==60, len(seen)
bad={m:re.findall(r'\b(?:sorry|admit|axiom|native_decide|ofReduceBool|unsafeCast|implemented_by)\b',code[modules[m]]) for m in seen}
assert not {m:v for m,v in bad.items() if v},bad
# No custom command/tactic/instance can redefine the basic mathematical language here.
custom={m:re.findall(r'^\s*(?:unsafe\s+)?(?:axiom|constant|opaque|instance|initialize|elab|macro|syntax|attribute)\b.*',code[modules[m]],re.M) for m in seen}
assert not {m:v for m,v in custom.items() if v},custom
comp=json.loads((P/'comparator.json').read_text())
assert comp['definition_names']==[]
assert comp['permitted_axioms']==['propext','Classical.choice','Quot.sound']
assert len(comp['theorem_names'])==25==len(set(comp['theorem_names']))
def header(text,name):
    r=re.search(r'^theorem\s+'+re.escape(name)+r'\b(.*?):=',text,re.M|re.S)
    return None if r is None else re.sub(r'\s+','',r.group(1))
contract_files={}
for full in comp['theorem_names']:
    name=full.split('.')[-1];expected=header(code['Challenge.lean'],name)
    assert expected is not None,full
    found=[m for m in seen if header(code[modules[m]],name) is not None]
    assert len(found)==1,(full,found)
    assert header(code[modules[found[0]]],name)==expected,full
    contract_files[full]=modules[found[0]]
assert len(re.findall(r'\bsorry\b',code['Challenge.lean']))==25
freeze=json.loads((P/'STATEMENT-FREEZE.json').read_text())
frozen=['Challenge.lean','NLA/PF03/Definitions.lean','NLA/PF03/RawData.lean','comparator.json','NUMERICAL_TARGETS.md']
assert all(sha(P/f)==freeze['sources'][f] for f in frozen)
meta=json.loads((P/'formalization.yaml').read_text())
assert [r['declaration'] for r in meta['status']['main_results']]==comp['theorem_names']
assert meta['verification']['canonical_verification_completed'] is False
assert meta['verification']['GitHub_Comparator']['status']=='NOT_RUN_FOR_THIS_PACKAGE'
assert all(not re.search(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}',(P/f).read_text()) for f in manifest['project_files'])
import jsonschema
schema=json.loads((BASE/'consulted/v0.4.schema.json').read_text())
jsonschema.validators.validator_for(schema)(schema).validate(meta)
# Read the coordinator's recorded local aggregate, without running Lean.
run=ROOT/'local-lean/runs/recovery-047'
receipt=json.loads((run/'RECEIPT.json').read_text())
record=next(r for r in receipt['commands'] if r['module']=='Solution')
assert receipt['end'] and record['exit_code']==0
assert record['source_sha256']==sha(P/'Solution.lean')
assert record['log_sha256']==sha(run/'Solution.log')
log=(run/'Solution.log').read_text()
axioms={n:sorted(a.strip() for a in ax.split(',')) for n,ax in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)}
assert set(axioms)==set(comp['theorem_names'])
assert all(a==sorted(comp['permitted_axioms']) for a in axioms.values())
# Actual package/compiler-source correspondence for every local implementation dependency.
commands={r['module']:r for r in receipt['commands']}
for m in seen:
    r=commands[m]
    assert r['source_sha256']==sha(P/modules[m]),m
    assert r.get('exit_code')==0 or r.get('status')=='reused_exact_successful_local_output',(m,r.keys())
report={
 'reviewer':'/root/pf03_final_referee2','kind':'Independent nonauthor AI source review; supplementary static audit; no Lean or Comparator execution',
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'sealed_handoff_sha256':sha(BASE/'STAGING-HANDOFF.json'),'sealed_files_checked':len(manifest['project_files']),
 'solution_source_sha256':sha(P/'Solution.lean'),'formalization_yaml_sha256':sha(P/'formalization.yaml'),
 'frozen_boundary_hashes':{f:sha(P/f) for f in frozen},
 'acyclic_solution_import_closure':sorted(seen),'external_imports':sorted(external),
 'implementation_module_count':len(seen)-1,'solution_imports_challenge':False,'implementation_forbidden_tokens':{},'custom_declaration_overrides':{},
 'reference_placeholder_count':25,'exact_whitespace_normalized_contract_headers':contract_files,
 'comparator_definition_holes':[],'metadata_schema':'Pinned formalization.yaml v0.4','schema_sha256':sha(BASE/'consulted/v0.4.schema.json'),
 'schema_validation':'PASS','email_pattern_scan':'No matches in the 74 sealed text files',
 'local_aggregate_observation':{'receipt_sha256':sha(run/'RECEIPT.json'),'log_sha256':sha(run/'Solution.log'),'command':record['argv'],'cwd':record['cwd'],'start':record['start'],'end':record['end'],'exit_code':record['exit_code'],'all_60_source_hashes_match_recorded_success_or_reuse':True,'observed_axioms':axioms,'rerun_by_this_reviewer':False,'recursive_reuse_origin_audit_by_this_script':False},
 'GitHub_Comparator_run_by_this_reviewer':False,'GitHub_Comparator_for_this_package':'UNRUN',
 'count_change':0,
 'all_packet_file_hashes':{f:sha(P/f) for f in manifest['project_files']},
}
(OUT/'STATIC-AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'sealed_files':len(manifest['project_files']),'implementation_modules':len(seen)-1,'headers_matched':len(contract_files),'schema_validation':'PASS','Solution_recorded_exit_code':record['exit_code'],'observed_axiom_reports':len(axioms),'audit_sha256':sha(OUT/'STATIC-AUDIT.json')},indent=2))
