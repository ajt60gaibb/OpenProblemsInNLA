from pathlib import Path
from datetime import datetime, timezone
import collections, copy, hashlib, json, re, subprocess, yaml

repo = Path('/tmp/nla-lean-mi03-worktree')
entry = repo/'matrix-inequalities-and-norms/MI-03'
project = entry/'lean'
pub = project/'verification/publication-2026-09-12'
linux = project/'verification/linux-2026-09-12'
work = Path('/tmp/nla-lean-formalization/mi03-publication')
sha = lambda b: hashlib.sha256(b).hexdigest()
fh = lambda p: sha(p.read_bytes())
git = lambda *a: subprocess.check_output(['git',*a],cwd=repo)
before = json.loads((pub/'before.json').read_text())
assert git('rev-parse','HEAD').decode().strip() == before['integrated_head']
identity = git('show','-s','--format=%an%x00%ae%x00%cn%x00%ce','HEAD').rstrip(b'\n').split(b'\0')
assert identity == [b'George Stepaniants',b'',b'George Stepaniants',b'']
prefix = str(project.relative_to(repo))+'/'
changes = {p:{'verified_sha256':h,'current_sha256':fh(project/p)} for p,h in before['all_verified_inputs'].items() if fh(project/p)!=h}
assert set(changes) == {'README.md','formalization.yaml'}
for p,h in before['all_verified_inputs'].items():
    assert h == sha(git('show',before['verified_revision']+':'+prefix+p)), p
for name,arch in [('README.md','README.linux-candidate.md'),('formalization.yaml','formalization.linux-candidate.yaml')]:
    assert fh(pub/'archive'/arch) == before['all_verified_inputs'][name], name
input_count = len(before['all_verified_inputs'])
unchanged_inputs = input_count-len(changes)
assert input_count == 173 and unchanged_inputs == 171
freeze = json.loads((project/'reviews/proof-freeze.json').read_text())
assert len(freeze['files']) == 101
for p,r in freeze['files'].items():
    if p=='README.md':
        assert fh(project/'verification/candidate-2026-09-12/README.statement.md') == r['sha256']
    else:
        assert fh(project/p) == r['sha256'] and (project/p).stat().st_size == r['bytes'], p
source_record = {}
assert len(freeze['source_files']) == 8
for p,h in freeze['source_files'].items():
    archived = linux/'source'/p
    assert fh(archived) == h and sha(git('show',freeze['source_commit']+':'+p)) == h, p
    current_changes = p in {str(entry.relative_to(repo))+'/'+n for n in ['README.md','problem.tex','problem.pdf']}
    if not current_changes: assert fh(repo/p) == h, p
    source_record[p] = {'original_sha256':h,'retained_snapshot':str(archived.relative_to(project)), 'current_publication_document':current_changes}
for p,h in before['all_operational_evidence'].items(): assert fh(project/p) == h, p
assert {str(p.relative_to(project)) for p in linux.rglob('*') if p.is_file()} == set(before['all_operational_evidence'])
outer = linux/'EVIDENCE-MANIFEST.json'
ev = json.loads(outer.read_text())
actual = {str(p.relative_to(linux)) for p in linux.rglob('*') if p.is_file() and p!=outer}
assert actual == set(ev['files'])
for p,r in ev['files'].items(): assert fh(linux/p) == r['sha256'] and (linux/p).stat().st_size == r['bytes'],p
op_count = len(before['all_operational_evidence'])
assert len(actual) == 303 and op_count == 304
canonical = (entry/'README.md').read_text()
tail = canonical[canonical.index('## Problem statement'):]
assert sha(tail.encode()) == before['canonical_target_tail_sha256']
for rev in [before['base'],before['verified_revision']]:
    s = git('show',rev+':matrix-inequalities-and-norms/MI-03/README.md').decode()
    assert s[s.index('## Problem statement'):] == tail
registry = json.loads((repo/'problem_ids.json').read_text())
assert fh(repo/'problem_ids.json') == before['problem_ids_sha256'] and len(registry) == 217
for ident,h in before['other_canonical'].items(): assert fh(repo/registry[ident]) == h, ident
assert len(before['other_canonical']) == 216
expected = {'CATALOG.md','README.md','RESOLVED.md','matrix-inequalities-and-norms/README.md',
            'matrix-inequalities-and-norms/MI-03/README.md','matrix-inequalities-and-norms/MI-03/problem.tex',
            'matrix-inequalities-and-norms/MI-03/problem.pdf','matrix-inequalities-and-norms/MI-03/lean/README.md',
            'matrix-inequalities-and-norms/MI-03/lean/formalization.yaml'}
actual_changes = set(git('diff','--name-only','HEAD').decode().splitlines())
assert actual_changes == expected, actual_changes^expected
preserved_base = []
for raw in git('ls-tree','-r','-z',before['base']).split(b'\0'):
    if not raw: continue
    metadata,path = raw.split(b'\t',1); mode,kind,oid = metadata.split(); p=path.decode()
    if p in expected: continue
    assert kind == b'blob' and mode in [b'100644',b'100755'], p
    f=repo/p; assert f.is_file() and not f.is_symlink(), p
    data=f.read_bytes()
    assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest() == oid.decode(),p
    preserved_base.append(p)
(pub/'preserved-upstream-files.json').write_text(json.dumps({'base':before['base'],'file_count':len(preserved_base),'unchanged_files':preserved_base},indent=2)+'\n')
def without_mi03_block(text):
    start=text.index('#### MI-03 — affirmative result'); end=text.index('\n#### ',start+6)
    return text[:start]+text[end:]
assert without_mi03_block((repo/'RESOLVED.md').read_text()) == without_mi03_block(git('show',before['base']+':RESOLVED.md').decode())
current = yaml.safe_load((project/'formalization.yaml').read_text())
original = yaml.safe_load((pub/'archive/formalization.linux-candidate.yaml').read_text())
remaining = copy.deepcopy(current)
fields = [('status','scope'),('review','status'),('review','notes'),('review','linux_verification','status'),('review','linux_verification','note')]
for ns in fields:
    a,b=remaining,original
    for n in ns[:-1]: a,b=a[n],b[n]
    assert a[ns[-1]] != b[ns[-1]], ns
    a[ns[-1]]=b[ns[-1]]
assert remaining == original
config=json.loads((project/'comparator.json').read_text())
assert [x['declaration'] for x in current['status']['main_results']] == config['theorem_names'] and len(config['theorem_names']) == 8
assert config.get('definition_names',[]) == []
assert current['project']['authors'] == ['George Stepaniants']
assert current['project']['affiliations']['George Stepaniants'] == 'Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'
for group in ['statement_reports','proof_reports']:
    for report in current['review'][group]: assert fh(project/report['file']) == report['sha256'],report
assert fh(project/current['review']['proof_freeze']['file']) == current['review']['proof_freeze']['sha256']
added='\n'.join(s[1:] for s in git('diff','--','*.md','*.yaml').decode().splitlines() if s.startswith('+') and not s.startswith('+++'))
assert not re.findall(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}',added)
counts = collections.Counter(re.search(r'^\*\*Status:\*\*\s+([^\n]+)',(repo/p).read_text(),re.M).group(1).strip() for p in registry.values())
expected_counts = dict(before['branch_counts_before']); expected_counts['Solved']-=1; expected_counts['Lean verified']+=1
assert dict(counts) == expected_counts
links=[]
for doc in [entry/'README.md',project/'README.md']:
    for link in re.findall(r'\]\(([^)]+)\)',doc.read_text()):
        if re.match(r'[a-z]+:',link): continue
        assert (doc.parent/link.split('#')[0]).exists(), (doc,link)
        links.append({'document':str(doc.relative_to(repo)),'link':link})
pdfinfo=(pub/'pdfinfo.log').read_text()
pages=int(re.search(r'^Pages:\s+(\d+)$',pdfinfo,re.M).group(1)); assert pages == 3
assert not re.search(r'Overfull|Missing character',(pub/'render.log').read_text())
text=subprocess.check_output(['pdftotext','-layout',str(entry/'problem.pdf'),'-']);(pub/'pdf-text.txt').write_bytes(text)
normalized_text = re.sub(r'\s+', ' ', re.sub(r'(?<=\w)-\s*\n\s*(?=\w)', '', text.decode()))
for required in ['Lean verified','Computing and Mathematical Sciences','California Institute of Technology','34722618003','modulus_semantics','odd_contraction_conjecture']:
    assert required in normalized_text, required
images=sorted((work/'pages').glob('page-*.png')); assert len(images) == pages
visual={'reviewer':'/root/formal_review_standards','result':'PASS: all three final PDF pages individually displayed and visually inspected',
        'observations':'Page 1 retains the original resolution, readable George Stepaniants/Caltech department credit, Colbrook/Bourin/Lee credit, all eight exports and actual verification scope. Page 2 shows pins, three reproducible commands and the exact original target/why-it-matters. Page 3 contains the unchanged references and historical search record. No clipping, overlap, missing glyphs or unreadable equations. References begin on the dedicated page selected by the unchanged repository renderer.',
        'pdf_sha256':fh(entry/'problem.pdf'),'rendered_images':{str(p):fh(p) for p in images}}
(pub/'visual-review.json').write_text(json.dumps(visual,indent=2)+'\n')
checks=[]
for name,args in [('diff-check',['git','diff','--check','HEAD']),('linux-evidence-preservation',['python3',str(linux/'verify_evidence.py')])]:
    r=subprocess.run(args,cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(pub/(name+'.log')).write_bytes(r.stdout)
    checks.append({'command':args,'exit_code':r.returncode,'log_sha256':sha(r.stdout)}); assert r.returncode == 0,r.stdout.decode()
(pub/'final-checks.json').write_text(json.dumps(checks,indent=2)+'\n')
record={'result':'PASS: ready for independent parent publication review; no publication commit or push',
        'created_utc':datetime.now(timezone.utc).isoformat(),'verified_revision':before['verified_revision'],'verified_run':before['verified_run'],
        'upstream_base':before['base'],'integration_commit':before['integrated_head'],'integration_author_email':'','integration_committer_email':'',
        'verified_input_count':input_count,'only_changed_verified_inputs':changes,'unchanged_verified_inputs':unchanged_inputs,
        'exact_prior_wrappers_archived':True,'unchanged_nonREADME_proof_freeze_inputs':len(freeze['files'])-1,
        'original_proof_freeze_README_archive_preserved':True,'all_eight_original_source_snapshots':source_record,
        'unchanged_operational_evidence_files':op_count,'outer_evidence_manifest_complete_including_nested':True,
        'all_216_other_canonical_pages_unchanged':True,'all_other_RESOLVED_blocks_unchanged':True,
        'unchanged_upstream_file_count':len(preserved_base),'original_target_and_references_tail_byte_identical':True,
        'original_informal_proof_and_all_shared_harness_files_unchanged':True,'permanent_ids':len(registry),
        'status_counts_before':before['branch_counts_before'],'status_counts_after':dict(counts),
        'metadata_changed_fields_only':['.'.join(p) for p in fields],'changed_tracked_files':sorted(expected),
        'changed_file_sha256':{p:fh(repo/p) for p in sorted(expected)},'local_links_checked':links,'no_email_added':True,
        'pdf_pages_visually_checked':pages,'prior_verifications_preserved':before['branch_counts_before']['Lean verified'],
        'reviewer_role_disclosure':'Publication preparer and operational auditor /root/formal_review_standards also served as statement referee 1 and final proof referee 1. No additional mathematical referee is implied; independent parent publication review remains pending.'}
(pub/'integrity.json').write_text(json.dumps(record,indent=2)+'\n')
(pub/'finish.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps({k:record[k] for k in ['result','integration_commit','unchanged_verified_inputs','unchanged_operational_evidence_files','unchanged_upstream_file_count','status_counts_after','pdf_pages_visually_checked']},indent=2))
