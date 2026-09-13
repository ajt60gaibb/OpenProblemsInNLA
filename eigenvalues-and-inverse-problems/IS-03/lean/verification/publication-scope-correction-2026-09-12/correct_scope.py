from pathlib import Path
import datetime, hashlib, json, subprocess

R = Path('/tmp/nla-lean-is03-worktree')
P = R / 'eigenvalues-and-inverse-problems/IS-03/lean'
O = P / 'verification/publication-2026-09-12'
E = P / 'verification/publication-scope-correction-2026-09-12'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(O / 'EVIDENCE-MANIFEST.json') == 'f01c38486feff1079f6366dd22e2b39437453d1b3040e102f1318876b1133b97'
old_manifest = json.loads((O / 'EVIDENCE-MANIFEST.json').read_text())
for name, entry in old_manifest['files'].items():
    assert sha(O / name) == entry['sha256'], name
    assert (O / name).stat().st_size == entry['bytes'], name
assert {p.relative_to(O).as_posix() for p in O.rglob('*') if p.is_file() and p != O / 'EVIDENCE-MANIFEST.json'} == set(old_manifest['files'])
integrity = json.loads((O / 'INTEGRITY-CHECKS.json').read_text())
for name, h in integrity['publication_sha256'].items():
    assert sha(R / name) == h, name
E.mkdir(exist_ok=False)
(E / 'correct_scope.py').write_bytes(Path(__file__).read_bytes())
changes = [
    ('eigenvalues-and-inverse-problems/IS-03/lean/formalization.yaml',
     'has no order-six realization\n',
     'has no entrywise-nonnegative order-six realization\n', 'formalization.yaml'),
    ('RESOLVED.md', 'impossibility of an exact-order-six realization.',
     'impossibility of an entrywise-nonnegative realization of exactly order six.', 'RESOLVED.md'),
]
rows = []
for relative, before, after, name in changes:
    p = R / relative
    old = p.read_text()
    assert old.count(before) == 1
    (E / (name + '.before.txt')).write_bytes(p.read_bytes())
    p.write_text(old.replace(before, after))
    (E / (name + '.after.txt')).write_bytes(p.read_bytes())
    rows.append({'file': relative, 'before': before, 'after': after,
                 'before_sha256': sha(E / (name + '.before.txt')), 'after_sha256': sha(p)})
commands = [
    ('manifest', ['/tmp/nla-lean-formalization/venv/bin/python', 'tools/lean/validate_manifest.py', 'eigenvalues-and-inverse-problems/IS-03/lean']),
    ('format', ['python3','tools/format_math.py','--check']),
    ('diff-whitespace', ['git', 'diff', '--check']),
]
checks=[]
for name, command in commands:
    result=subprocess.run(command,cwd=R,capture_output=True)
    log=E/(name+'.log');log.write_bytes(result.stdout+result.stderr)
    checks.append({'command':command,'exit_code':result.returncode,'log':log.name,'log_sha256':sha(log)})
    assert result.returncode==0,log.read_text()[:4000]
for relative,h in integrity['publication_sha256'].items():
    if relative not in {x[0] for x in changes}: assert sha(R/relative)==h,relative
for relative,h in integrity['unchanged_nonwrapper_sha256'].items(): assert sha(P/relative)==h,relative
for key,value in integrity.items():
    if isinstance(value,dict) and key.endswith('sha256') and key not in {'publication_sha256','unchanged_nonwrapper_sha256'}:
        for relative,h in value.items():
            if isinstance(h,str) and len(h)==64:
                assert sha(P/relative)==h,(key,relative)
for name,entry in old_manifest['files'].items(): assert sha(O/name)==entry['sha256'],name
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'verdict':'PASS: two publication-only scope qualifications; independent publication review still pending',
    'finding_by':'/root/leancert_examples', 'correction_by':'/root',
    'finding':'Two standalone descriptions omitted entrywise nonnegativity. Arbitrary real companion realizations are not excluded by the theorem.',
    'initial_publication_manifest_sha256':sha(O/'EVIDENCE-MANIFEST.json'),
    'initial_publication_integrity_sha256':sha(O/'INTEGRITY-CHECKS.json'),
    'changes':rows,'checks':checks,
    'current_publication_sha256':{f:sha(R/f) for f in integrity['publication_sha256']},
    'preservation':'Initial sealed publication evidence unchanged. All301 nonwrapper candidate inputs and452 operational files unchanged. Seven other publication outputs including canonical README/TeX/PDF unchanged; no mathematical/config/source/gate change.',
    'no_new_Lean_Linux_or_PDF_execution':True}
(E/'CORRECTION.json').write_text(json.dumps(record,indent=2)+'\n')
(E/'SCOPE-CORRECTION.md').write_text('''# IS-03 publication scope clarification

Independent publication review by `/root/leancert_examples` found that two standalone descriptions omitted **entrywise nonnegativity** from the excluded realization. `/root` corrected exactly the status.scope sentence in formalization.yaml and the new IS-03 RESOLVED paragraph. The actual theorem excludes entrywise-nonnegative real order-six realizations; it does not exclude arbitrary real companion realizations.

The original sealed publication package is retained unchanged and records the preceding wording. `CORRECTION.json` and exact before/after snapshots document the two replacements and current publication hashes. Fresh schema/full-export coverage, global math formatting and tracked diff whitespace checks passed. Every other publication output, all301 nonwrapper candidate inputs, all452 operational files and all mathematical/configuration/source bytes are unchanged. The canonical PDF is unchanged, so its existing three-page visual evidence remains applicable. This correction adds no mathematical referee or new Lean/Linux execution. Independent publication approval remains a separate step.
''')
files={q.relative_to(E).as_posix():{'sha256':sha(q),'bytes':q.stat().st_size} for q in sorted(E.rglob('*')) if q.is_file()}
(E/'EVIDENCE-MANIFEST.json').write_text(json.dumps({'file_count':len(files),'files':files,'inventory_rule':'Every file in this directory except this exact outer manifest; all nested manifests included.'},indent=2)+'\n')
print(json.dumps({'status':'PASS','correction_sha256':sha(E/'CORRECTION.json'),'manifest_sha256':sha(E/'EVIDENCE-MANIFEST.json'),'files':len(files),'changes':rows},indent=2))
