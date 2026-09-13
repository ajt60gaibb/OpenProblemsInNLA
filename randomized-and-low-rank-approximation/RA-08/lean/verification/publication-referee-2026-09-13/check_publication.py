"""Independent read-only RA-08 publication integrity review.

Writes only this referee's separate evidence. Does not rerun Lean, edit any
publication wrapper, regenerate a catalog/PDF, or mutate Git state.
"""
from pathlib import Path
import collections, datetime, hashlib, json, re, shutil, subprocess
import yaml

E = Path(__file__).resolve().parent
P = E.parents[1]
W = P.parents[2]
PREFIX = 'randomized-and-low-rank-approximation/RA-08/lean'
CANDIDATE = 'de6513d726e3f66d20730fdaef5ba99318ee7e8b'
BASE = '5830ed4fb06da0659414a3deb2a40ad327aca052'
PUB = P / 'verification/publication-2026-09-13'
OPS = P / 'verification/linux-2026-09-12'
ROOT = P / 'verification/root-operational-2026-09-12'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
digest = lambda raw: hashlib.sha256(raw).hexdigest()
git = lambda *args: subprocess.check_output(['git', *args], cwd=W)
load = lambda p: json.loads(Path(p).read_text())
known = {
    PUB / 'PUBLICATION-HANDOFF.md': '81c83a2fe55a7bba90bb28ff81763c523317984cb21b77c79e7a8ce0dd5ed858',
    PUB / 'INTEGRITY-CHECKS.json': '532a982468b7e9c20c6c8cfcd50bbdc0de619ad564c96569d5ce674bb3a2d5e0',
    PUB / 'EVIDENCE-MANIFEST.json': 'fa1f504d8223cdb42581197e07b64d21a0a014eacb1dc49915ee964f32aca227',
    OPS / 'OPERATIONAL-REVIEW.md': '2b16b9952c15f070810756159990cc90745afaa7ad5ac22c3d022cce6b91cffe',
    OPS / 'EVIDENCE-MANIFEST.json': '072e05a2022b16ffbf259ca5cfdf6b47929865aad70c8ba20d1a3ac38c31ce1b',
    P / 'verification/proof-freeze.json': 'ab05e2bf801e6906453e88a4d84d5e73191f776db05610fb8b8e5e4a03d4f856',
    P / 'reviews/statement-freeze.json': 'eb0460c3dd4c13a42f928e3f00c9c3710e486922b99aff74f4d6a3098c5ed332',
    ROOT / 'ROOT-CHECKS.json': 'a1fb7ac0b4bfebb5cd1e536ac7b5d78f3beb82b6ca4d1486ca0f3c293d9b3c12',
    P / 'reviews/final-referee-1.md': 'a19a55d07e1aeafd1b73116b1c217024431f3f2d0b31fa5939b143194651be2f',
    P / 'reviews/final-referee-2.md': '31f69c8bf835848cc45ac475fd6449d24e5daf19b3daa6a30286c204a3294c5b',
}
for p, h in known.items():
    assert sha(p) == h, p
assert git('rev-parse','HEAD').decode().strip() == CANDIDATE
assert git('show','-s','--format=%an%n%ae%n%cn%n%ce',CANDIDATE).decode().splitlines() == ['George Stepaniants','','George Stepaniants','']

inventory_counts = {}
for d in [PUB, OPS, ROOT]:
    outer = d / 'EVIDENCE-MANIFEST.json'
    manifest = load(outer)
    actual = {str(p.relative_to(d)) for p in d.rglob('*') if p.is_file() and p != outer}
    assert actual == set(manifest['files']), d
    for name, row in manifest['files'].items():
        assert sha(d / name) == row['sha256'], name
        if 'bytes' in row:
            assert (d / name).stat().st_size == row['bytes']
    inventory_counts[str(d.relative_to(P))] = {'bound':len(actual),'including_outer':len(actual)+1,
        'outer_sha256':sha(outer), 'nested_manifests_preserved':sum(Path(n).name=='EVIDENCE-MANIFEST.json' for n in actual)}
assert inventory_counts[str(OPS.relative_to(P))]['including_outer'] == 793
assert inventory_counts[str(ROOT.relative_to(P))]['including_outer'] == 7
assert inventory_counts[str(PUB.relative_to(P))]['including_outer'] == 23

paths = git('ls-tree','-r','--name-only',CANDIDATE,PREFIX).decode().splitlines()
assert len(paths) == 613
candidate_records = {}
archive_map = {'README.md':'archive/README.linux-candidate.md',
               'formalization.yaml':'archive/formalization.linux-candidate.yaml'}
for name in paths:
    rel = name[len(PREFIX)+1:]
    raw = git('show',CANDIDATE+':'+name)
    saved = OPS / 'source' / name
    assert saved.read_bytes() == raw, name
    current = PUB / archive_map[rel] if rel in archive_map else P / rel
    assert current.read_bytes() == raw, rel
    candidate_records[rel] = {'sha256':digest(raw),'git_blob':git('rev-parse',CANDIDATE+':'+name).decode().strip(),
                               'current_exact_location':str(current.relative_to(P))}
assert set(load(PUB/'before.json')['project_inputs']) == set(candidate_records)
for rel, data in candidate_records.items():
    assert load(PUB/'before.json')['project_inputs'][rel] == data['sha256']
frozen_records = {}
for fn in ['verification/proof-freeze.json','reviews/statement-freeze.json']:
    f = load(P/fn)
    for name, expected in f['files'].items():
        historical = {'README.md':'verification/pre-candidate-README.md','formalization.yaml':'verification/pre-candidate-formalization.yaml'}
        actual = P / historical.get(name,name)
        assert sha(actual) == expected, (fn,name)
    frozen_records[fn] = {'sha256':sha(P/fn),'preserved_files':len(f['files']),
                         'historical_wrapper_mappings':historical}
    for name, expected in f['source_files'].items():
        raw = git('show',f['base']+':'+name)
        assert digest(raw) == expected
        assert (OPS/'source'/name).read_bytes() == raw, name
assert frozen_records['verification/proof-freeze.json']['preserved_files']==450
assert frozen_records['reviews/statement-freeze.json']['preserved_files']==39

def changed(a,b,prefix=''):
    if isinstance(a,dict) and isinstance(b,dict):
        out=[]
        for k in sorted(set(a)|set(b)):
            p=(prefix+'.' if prefix else '')+str(k)
            if k not in a or k not in b: out.append(p)
            else: out+=changed(a[k],b[k],p)
        return out
    return [] if a==b else [prefix]
before_y=yaml.safe_load((PUB/archive_map['formalization.yaml']).read_text())
after_y=yaml.safe_load((P/'formalization.yaml').read_text())
fields=changed(before_y,after_y)
assert set(fields)=={'status.scope','review.status','review.notes','review.linux_verification.status','review.linux_verification.note'},fields
cfg=load(P/'comparator.json')
assert len(cfg['theorem_names'])==14 and cfg['definition_names']==[]
assert [d['declaration'] for d in after_y['status']['main_results']]==cfg['theorem_names']
assert all(d['sorry_count']==0 for d in after_y['status']['main_results'])
assert after_y['status']['sorry_count']==0 and after_y['status']['sorry_in_definitions']==0
assert set(after_y['status']['axioms'])=={'propext','Classical.choice','Quot.sound'}
assert after_y['project']['authors']==['George Stepaniants']
aff='Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'
assert after_y['project']['affiliations']['George Stepaniants']==aff

expected={'CATALOG.md','README.md','RESOLVED.md','randomized-and-low-rank-approximation/README.md',
          'randomized-and-low-rank-approximation/RA-08/README.md','randomized-and-low-rank-approximation/RA-08/problem.pdf',
          'randomized-and-low-rank-approximation/RA-08/problem.tex',PREFIX+'/README.md',PREFIX+'/formalization.yaml'}
assert set(git('diff','--name-only',CANDIDATE).decode().splitlines())==expected
publication_hashes={name:sha(W/name) for name in sorted(expected)}
assert publication_hashes==load(PUB/'INTEGRITY-CHECKS.json')['publication_files']
registry=json.loads(git('show',BASE+':problem_ids.json'))
assert len(registry)==217 and (W/'problem_ids.json').read_bytes()==git('show',BASE+':problem_ids.json')
other=0;counts=collections.Counter()
for pid,name in registry.items():
    raw=(W/name).read_bytes();text=raw.decode()
    counts[re.search(r'\*\*Status:\*\*\s*([^\n]+)',text).group(1).strip()]+=1
    if pid!='RA-08':assert raw==git('show',BASE+':'+name),name;other+=1
canon=registry['RA-08'];old=git('show',BASE+':'+canon)
marker=b'Let $`n\\ge2`$'
assert (W/canon).read_bytes().split(marker,1)[1]==old.split(marker,1)[1]
resolved_before=git('show',BASE+':RESOLVED.md').decode();resolved_after=(W/'RESOLVED.md').read_text()
def without_ra08(text):
    a=text.index('**RA-08 (');b=text.index('\n\n**RA-09 (',a)
    return text[:a]+'<RA08_REVIEWED_PARAGRAPH>'+text[b:]
assert without_ra08(resolved_before)==without_ra08(resolved_after)
assert dict(counts)=={'Solved':75,'Open':53,'Partially resolved':72,'Lean verified':17}
added='\n'.join(l[1:] for l in git('diff','--unified=0',CANDIDATE).decode(errors='replace').splitlines()
                if l.startswith('+') and not l.startswith('+++'))
assert not re.search(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}',added)

# Independent examination of the retained actual run identity and acceptance.
run=load(ROOT/'observed-run.json');jobs=load(ROOT/'observed-jobs.json')['jobs']
assert run['id']==34735273999 and run['head_sha']==CANDIDATE
assert run['status']=='completed' and run['conclusion']=='success' and len(jobs)==17
assert all(j['conclusion']=='success' and all(s['conclusion']=='success' for s in j['steps']) for j in jobs)
actual=list((OPS/'artifacts/lean-RA-08').rglob('result.json'))
assert len(actual)==1
receipt=load(actual[0]);(E/'actual-project-receipt.json').write_bytes(actual[0].read_bytes())
comparator=actual[0].parent/'comparator.log'
raw_log=comparator.read_text()
assert 'Lean default kernel accepts the solution' in raw_log and 'Your solution is okay!' in raw_log
axiom_reports=re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]",raw_log,re.S)
assert len(axiom_reports)==59
assert all({a.strip() for a in aa.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,aa in axiom_reports)
for name in cfg['theorem_names']:
    assert raw_log.count(name)>=2,name

visual=load(PUB/'VISUAL-REVIEW.json')
pdf=W/'randomized-and-low-rank-approximation/RA-08/problem.pdf';tex=pdf.with_suffix('.tex')
assert sha(pdf)==visual['pdf_sha256']=='01976dbb5e921095c7b14fdb60727dd21cd2e2565f947aef75545ae1f1153669'
assert sha(tex)==visual['tex_sha256']=='966f3f7c9c678f6c62b3f37bd4ca481b21d5f0ef079003ec7e365f2fe809ea71'
images={}
for n in [1,2,3]:
    image=Path('/tmp/nla-lean-formalization/ra08-publication-pages')/f'page-{n}.png'
    assert sha(image)==visual['images'][image.name]
    (E/'pages').mkdir(exist_ok=True)
    shutil.copyfile(image,E/'pages'/image.name)
    images[image.name]=sha(image)
for row in load(PUB/'checks.json'):
    assert row['exit_code']==0 and sha(PUB/row['log'])==row['log_sha256']
assert 'Ran 17 tests' in (PUB/'permanent-id-tests.log').read_text()
for name in ['permanent-ids-origin.log','permanent-ids-upstream.log','manifest.log','format-check.log','render.log','pdfinfo.log']:
    (E/name).write_bytes((PUB/name).read_bytes())
(E/'candidate-input-checks.json').write_text(json.dumps(candidate_records,indent=2)+'\n')
(E/'publication-diff.patch').write_bytes(git('diff',CANDIDATE))
result={'verdict':'PASS independent publication integrity review; semantic and actual visual findings in adjacent report',
        'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewer':'/root/formal_review_standards',
        'role':'Publication reviewer separate from current preparer; disclosed main mathematical coauthor, not independent mathematical referee and no extra mathematical approval',
        'candidate':CANDIDATE,'base':BASE,'candidate_inputs':613,'preserved_nonwrapper_inputs':611,
        'exact_candidate_wrappers_archived':2,'changed_yaml_fields':fields,'frozen_inputs':frozen_records,
        'original_Git_sources':10,'complete_inventories':inventory_counts,'other_canonical_pages_preserved':other,
        'permanent_registry_entries':217,'original_target_suffix_preserved':True,
        'only_RA08_RESOLVED_paragraph_changed':True,'status_counts':dict(counts),
        'publication_files':publication_hashes,'actual_run':run['id'],'all_actual_jobs_and_steps_pass':17,
        'actual_comparator_log_sha256':sha(comparator),'embedded_standard_three_reports':59,
        'fourteen_export_names':cfg['theorem_names'],'definition_exceptions':[],
        'pdf_pages_actually_displayed_and_reviewed':[1,2,3],'retained_displayed_pngs':images,
        'new_mathematical_compile_or_Linux_run':False,'canonical_or_wrapper_edit':False,
        'Git_mutation_or_publication':False,'George_email_on_new_lines':False}
(E/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'verdict':'PASS','candidate_inputs':613,'nonwrapper_inputs':611,'operational_files':800,
                  'frozen_proof_inputs':450,'frozen_statement_inputs':39,'all_three_PDF_pages':True,
                  'CHECKS_sha256':sha(E/'CHECKS.json')},indent=2))
