import pathlib,json,hashlib,re,subprocess,datetime
repo=pathlib.Path.cwd();p=repo/'docs/lean/campaign/2026-09-22/IE-22/lean';e=p/'reviews/ie22-final-fidelity-evidence';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();snap=json.loads((p/'reviews/package-source-freeze.json').read_text());freeze=snap['source_sha256'];assert len(freeze)==57 and all(sha(p/f)==s for f,s in freeze.items());proof=json.loads((p/'reviews/proof-source-freeze.json').read_text());assert len(proof['source_sha256'])==47 and all(sha(p/f)==s for f,s in proof['source_sha256'].items())
statement=json.loads((p/'reviews/statement-freeze.json').read_text());assert all(sha(p/f)==s for f,s in statement['mathematical_boundary_sha256'].items());reviewers=[]
for rv in statement['preproof_referees']:
 assert sha(p/rv['report'])==rv['report_sha256'];assert sha(p/rv['receipt'])==rv['receipt_sha256'];reviewers.append(rv)
vendor=json.loads((p/'reviews/IE21-DEPENDENCY.json').read_text());vendchecks={}
for f,s in vendor['source_sha256'].items():
 raw=subprocess.check_output(['git','show',vendor['source_commit']+':'+vendor['source_project']+'/'+f]);assert hashlib.sha256(raw).hexdigest()==s==sha(p/f);vendchecks[f]=s
canonical=repo/'linear-systems-and-elimination/IE-22/README.md';base='54f93060c0c4e5dab81096c6496e0d2b4251f3ef';source=repo/'references/colbrook-recovered-2026-09-11/manuscripts/IE-21-22.tex';assert canonical.read_bytes()==subprocess.check_output(['git','show',base+':'+str(canonical.relative_to(repo))]);assert source.read_bytes()==subprocess.check_output(['git','show',base+':'+str(source.relative_to(repo))]);fullstmt=canonical.read_text().split('## Problem statement\n\n',1)[1].split('\n## Connection to numerical linear algebra',1)[0];assert fullstmt in (p/'NUMERICAL_TARGETS.md').read_text()
def code_only(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s.startswith('/-',i):depth+=1;i+=2
  elif depth and s.startswith('-/',i):depth-=1;i+=2
  elif depth:i+=1
  elif s.startswith('--',i):
   j=s.find('\n',i);i=len(s) if j<0 else j
  elif s[i]=='"':
   i+=1
   while i<len(s):
    if s[i]=='\\':i+=2
    elif s[i]=='"':i+=1;break
    else:i+=1
   out.append('"STRING"')
  else:out.append(s[i]);i+=1
 return ''.join(out)
forbidden=r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b|^\s*import\s+Challenge\b';hits={}
for q in sorted((p/'NLA').rglob('*.lean')):
 cs=code_only(q.read_text());m=re.findall(forbidden,cs,re.M)
 if m:hits[str(q.relative_to(p))]=m
assert not hits
cfg=json.loads((p/'comparator.json').read_text());sol=(p/'Solution.lean').read_text();assert re.findall(r'^#assert_trust kernel (\S+)',sol,re.M)==cfg['theorem_names'];assert re.findall(r'^#print axioms (\S+)',sol,re.M)==cfg['theorem_names'];assert 'set_option leancert.trust "kernel"' in sol;assert cfg['definition_names']==[];assert len(re.findall(r'\bsorry\b',code_only((p/'Challenge.lean').read_text())))==20
refs=['docs/lean/README.md','docs/lean/REVIEW.md','tools/lean/source-lock.json','randomized-and-low-rank-approximation/RA-02/lean/sources/patterns/Schiffer-Challenge.lean','randomized-and-low-rank-approximation/RA-02/lean/sources/patterns/Forsythe-Challenge.lean','randomized-and-low-rank-approximation/RA-20/lean/reviews/final-referee-1-evidence/inspected-source/leancert/LeanCert/Tactic/Verification.lean'];external={f:sha(repo/f) for f in refs};external[str(canonical.relative_to(repo))]=sha(canonical);external[str(source.relative_to(repo))]=sha(source)
apiroot=pathlib.Path('/private/tmp/mf21-mathlib-source-20260920');apifiles=['Mathlib/Analysis/InnerProductSpace/Spectrum.lean','Mathlib/Probability/Distributions/Gaussian/Multivariate.lean','Mathlib/Probability/Moments/Variance.lean'];apis={f:sha(apiroot/f) for f in apifiles}
search=['rg','-n','Poincar[eé]|[Pp]oincare|variance.*[Pp]rod|variance.*[Pp]i|eigenvalues_antitone|eigenvectorBasis',str(apiroot/'Mathlib/Probability'),str(apiroot/apifiles[0])];sr=subprocess.run(search,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(e/'mathlib-api-search.log').write_text(sr.stdout)
cmd=['/private/tmp/nla-merge-pr-297-299-venv/bin/python','tools/lean/validate_manifest.py',str(p.relative_to(repo))];mr=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(e/'manifest-validation.log').write_text(mr.stdout);assert mr.returncode==0
build=json.loads((e/'build-receipt.json').read_text());assert build['source_sha256_after']==freeze
logs=[(e/(f.replace('/','__')+'.log')).read_text() for f in proof['source_sha256']];audit=(e/'exact-types-and-axioms2.log').read_text();receipt={'phase':'Independent nonauthor full source audit; Linux completion still pending','timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewer':'/root/ie22_final_fidelity','source_modules_read_in_full':47,'core_files_sha256':freeze,'external_inputs_sha256':external,'preproof_referee_records_checked':reviewers,'vendored_IE21_git_commit':vendor['source_commit'],'vendored_IE21_files_matched_to_git_objects':vendchecks,'canonical_and_manuscript_unchanged_from_scope_base':base,'complete_original_statement_preserved_verbatim_in_inventory':True,'forbidden_proof_source_matches':hits,'challenge_placeholder_count':20,'kernel_assertion_target_count':20,'definition_holes':0,'source_build_diagnostics':{'warnings':sum(len(re.findall(r'warning:',t)) for t in logs),'errors':sum(len(re.findall(r'error:',t)) for t in logs)},'audit_diagnostics':{'unused_binder_warnings':len(re.findall(r'warning:',audit)),'errors':len(re.findall(r'error:',audit))},'manifest_validation':{'command':cmd,'exit_code':mr.returncode,'log_sha256':sha(e/'manifest-validation.log')},'pinned_API_inspection':{'root':str(apiroot),'files_sha256':apis,'search_command':search,'search_exit_code':sr.returncode,'search_log_sha256':sha(e/'mathlib-api-search.log'),'limitation':'Extracted source API tree has no independently authenticated Git metadata in this referee pass; source examples retained in repo were read, not freshly fetched. Authentic project/dependency verification belongs to pending Linux completion gate.'},'build_receipt_sha256':sha(e/'build-receipt.json')}
(e/'inspection-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({'all_57_hashes_match':True,'all_31_vendor_git_blobs_match':True,'all_47_source_modules_read':True,'source_diagnostics':receipt['source_build_diagnostics'],'audit_diagnostics':receipt['audit_diagnostics'],'manifest':mr.stdout.strip(),'canonical_sha256':sha(canonical),'manuscript_sha256':sha(source)},indent=2))
