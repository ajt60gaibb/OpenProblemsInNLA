from pathlib import Path
import collections,datetime,hashlib,json,re,subprocess,yaml
R=Path.cwd();P=R/'linear-systems-and-elimination/IE-22/lean';O=P/'reviews/ie22-final-fidelity-evidence'
base='19d9f19bd2b779caf5f3b40540e9a303a1226a5c';cand='bbc8a4ce709582095317efb16a5acc48cb7455c3';source='c45f9ccef20a2fa5cc4b988e93d4173dab853362'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.check_output(['git',*a],cwd=R)
def blob(c,p):return git('show',c+':'+p)
assert git('rev-parse','HEAD').decode().strip()==cand
reg=blob(cand,'problem_ids.json');assert reg==blob(base,'problem_ids.json');ids=json.loads(reg);assert len(ids)==217
counts=collections.Counter(); canonical='linear-systems-and-elimination/IE-22/README.md'
for ident,path in ids.items():
 a,b=blob(base,path),blob(cand,path)
 assert ident=='IE-22' or a==b,(ident,path)
 counts[re.search(rb'^\*\*Status:\*\* (.*?)\s*$',b,re.M).group(1).decode()]+=1
assert dict(counts)=={'Lean verified':66,'Solved':40,'Partially resolved':70,'Open':41},counts
old=blob(base,canonical).decode();new=blob(cand,canonical).decode()
stripped=re.sub(r'## Lean proof and verification evidence - 2026-09-22\n\n.*?(?=## Problem statement\n)', '',new,flags=re.S)
stripped=stripped.replace('**Status:** Lean verified','**Status:** Solved').replace('**Last checked:** 2026-09-22','**Last checked:** 2026-09-11')
assert stripped==old
resolved=blob(cand,'RESOLVED.md').decode();restored=re.sub(r'\*\*IE-22 Lean verification, 2026-09-22\.\*\*[^\n]*\n\n','',resolved)
assert restored==blob(base,'RESOLVED.md').decode()
assert blob(base,'references/colbrook-recovered-2026-09-11/manuscripts/IE-21-22.tex')==blob(cand,'references/colbrook-recovered-2026-09-11/manuscripts/IE-21-22.tex')
assert 'https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/'+source+'/linear-systems-and-elimination/IE-22/lean/NLA/IE22/Final.lean' in new
assert 'https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/'+source+'/linear-systems-and-elimination/IE-22/lean' in resolved
prefix=P.relative_to(R).as_posix(); freeze=json.loads((P/'reviews/package-source-freeze.json').read_text())['source_sha256']; core={k:v for k,v in freeze.items() if k not in ['README.md','formalization.yaml']};assert len(core)==55
for n,h in core.items():assert sha(blob(cand,prefix+'/'+n))==h==sha((P/n).read_bytes()),n
sourcefiles=git('ls-tree','-r','--name-only',source,'--',prefix).decode().splitlines();assert len(sourcefiles)==394
changed_source=[]
for n in sourcefiles:
 if blob(source,n)!=blob(cand,n):changed_source.append(n[len(prefix)+1:])
assert sorted(changed_source)==['README.md','formalization.yaml']
linux=P/'verification/linux';manifest=json.loads((linux/'evidence-manifest.json').read_text())['files'];assert len(manifest)==455
assert sha((linux/'evidence-manifest.json').read_bytes())=='a26606cc445414a8532aa1337ca5df6d0cb047dd1b42e416afed9fd8cac2a9e7'
for n,h in manifest.items():assert sha(blob(cand,prefix+'/verification/linux/'+n))==h==sha((linux/n).read_bytes()),n
metadata=yaml.safe_load(blob(cand,prefix+'/formalization.yaml'));assert metadata['version']=='v0.4'
assert metadata['project']['authors']==['George Stepaniants']
affiliation='Department of Computing and Mathematical Sciences, California Institute of Technology'
assert metadata['project']['affiliations']=={'George Stepaniants':affiliation}
assert metadata['status']['verified_source_commit']==source and metadata['status']['completed_target_count']==20
assert metadata['status']['sorry_count']==0 and metadata['status']['sorry_in_definitions']==0 and metadata['status']['challenge_placeholder_count']==20
assert metadata['status']['authoritative_linux_result']=='passed' and metadata['status']['comparator_result']=='comparator-accepted'
config=json.loads(blob(cand,prefix+'/comparator.json'));names=config['theorem_names'];assert len(names)==20
assert [p['declaration'] for p in metadata['status']['main_results']]==names
for p in metadata['status']['main_results']:
 assert p['sorry_count']==0 and set(p['axioms'])=={'propext','Classical.choice','Quot.sound'}
 assert re.search(r'^theorem '+re.escape(p['declaration'].split('.')[-1])+r'\b',blob(cand,prefix+'/'+p['file']).decode(),re.M),p
pubpaths=['CATALOG.md','README.md','RESOLVED.md',canonical,'linear-systems-and-elimination/IE-22/problem.tex','linear-systems-and-elimination/IE-22/problem.pdf','linear-systems-and-elimination/README.md','tools/render_problems.py',prefix+'/README.md',prefix+'/formalization.yaml']
for n in pubpaths:
 assert (R/n).read_bytes()==blob(cand,n),n
 if n.endswith(('.md','.yaml')) and n in [canonical,prefix+'/README.md',prefix+'/formalization.yaml']:
  txt=blob(cand,n).decode();assert affiliation in txt and 'George Stepaniants' in txt and 'Matthew J. Colbrook' in txt
  assert not re.search(r'\b[^\s<>]+@[^\s<>]+\.[A-Za-z]{2,}\b',txt),n
for n in ['README.md','CATALOG.md']:
 assert '**Resolution evidence:** 40 solved (published or independently audited); 66 solved with Lean verification.' in blob(cand,n).decode()
outs=set(git('diff','--name-only',base,cand,'--',':!'+prefix+'/**').decode().splitlines());assert outs==set(pubpaths[:8]),outs
pdf=R/'linear-systems-and-elimination/IE-22/problem.pdf';assert sha(pdf.read_bytes())=='0b58c390d68651b738a9af42dff4841bd20bf5b167a8c0279d787245ddd0a216'
assert re.search(r'^Pages:\s+3$',subprocess.check_output(['pdfinfo',str(pdf)],text=True),re.M)
qa={p.name:sha(p.read_bytes()) for p in Path('/private/tmp/nla-ie22-fidelity-publication-pdf').glob('page-*.png')};assert len(qa)==3
# Range-wide historical evidence diagnostic whitespace is preserved and recorded, not repaired.
full=subprocess.run(['git','diff','--check',base,cand],cwd=R,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
(O/'publication-full-range-whitespace.log').write_text(full.stdout);assert full.returncode!=0
scoped=subprocess.run(['git','diff','--check',base,cand,'--',*pubpaths],cwd=R,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
(O/'publication-documentation-whitespace.log').write_text(scoped.stdout);assert scoped.returncode==0
# Every full-range whitespace diagnostic is inside historical review/verification data.
paths=re.findall(r'^([^\n]+?):\d+: (?:trailing whitespace|new blank line at EOF|space before tab in indent)\.',full.stdout,re.M)
assert paths and all(n.startswith(prefix+'/reviews/') or n.startswith(prefix+'/verification/') for n in paths),set(paths)
receipt={'reviewer':'/root/ie22_final_fidelity','AI_agent':True,'independent_nonauthor':True,'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'candidate_commit':cand,'base_commit':base,'verified_source_commit':source,'result':'PASS','canonical_original_reconstructed_exactly':True,'resolved_only_additive_notice':True,'original_manuscript_unchanged':True,'registry_ids_unchanged':217,'other_canonical_pages_unchanged':216,'canonical_status_counts':dict(counts),'frozen_mathematical_core_files_unchanged':55,'all392_nondocumentation_original_inputs_unchanged':True,'only_changed_verified_input_files':changed_source,'all455_frozen_linux_evidence_files_unchanged':True,'metadata_v04_all20_complete_targets_match':True,'exact_george_affiliation_no_contact_email_preserved_colbrook':True,'pdf_sha256':sha(pdf.read_bytes()),'pdf_pages':3,'independent_96dpi_pdf_render_images':qa,'independent_visual_review':'All three independently rerendered pages read; no clipping, overlap, lost symbols or missing original statement/history found.','full_range_diff_check_exit':full.returncode,'full_range_whitespace_log_sha256':sha(full.stdout.encode()),'publication_documentation_diff_check_exit':scoped.returncode,'historical_whitespace_files':sorted(set(paths)),'publication_file_sha256':{n:sha(blob(cand,n)) for n in pubpaths}}
(O/'publication-audit-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k not in ['historical_whitespace_files','publication_file_sha256']},indent=2))
