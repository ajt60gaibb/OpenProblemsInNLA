from pathlib import Path
import hashlib, json

source = Path('/tmp/nla-lean-formalization/accept_ra08_linux.py')
out = Path('/tmp/nla-lean-formalization/accept_ra09_linux.py')
assert not out.exists()
s = source.read_text().replace('RA-08', 'RA-09').replace("'tree': 'ra08'", "'tree': 'ra09'")
replacements = {
    'de6513d726e3f66d20730fdaef5ba99318ee7e8b': '3bcc863070c037fffb1deee3f12d1cd1517727df',
    '34735273999': '34738884548', '34735273988': '34738884555',
    "'inputs': 613": "'inputs': 524", "'axioms': 59": "'axioms': 49",
    '[2710, 3161]': '[2710, 2726]', "'evidence_count': 792": "'evidence_count': 703",
    '072e05a2022b16ffbf259ca5cfdf6b47929865aad70c8ba20d1a3ac38c31ce1b': '56dd2e10ca4d4f16367f85d06fde4630f66df2e4ac12dfbace9637e97b49de90',
    '2b16b9952c15f070810756159990cc90745afaa7ad5ac22c3d022cce6b91cffe': '56aec1e09de54a0b0aea0545fc6fd0fc54f2c5d5e4b52c1e8b3870ade5d66a0d',
    "'freeze_count': 450": "'freeze_count': 361", '2026-09-12': '2026-09-13',
    "len(freeze['source_files']) == 10": "len(freeze['source_files']) == 17",
    "'original_source_Git_blobs': 10": "'original_source_Git_blobs': 17",
    "len(config['theorem_names']) == 14": "len(config['theorem_names']) == 17",
    "log.count('warning: Challenge.lean:') == 14": "log.count('warning: Challenge.lean:') == 17",
    'The two independent mathematical referees are leancert_examples and mf16_final_referee': 'The two independent mathematical referees are ra09_final_referee1 and mf16_final_referee',
    'Material explicit-kernel LeanCert strict-upper checker for zero on [0,0] below the exact rational gap, consumed through actual CFC and Euclidean Rayleigh bound to the full original all-parameter/all-function/all-basis negation.': 'Exact scalar and finite matrix reasoning with real LeanCert kernel trust/dependency assertions; no artificial interval computation. Full original trace-deficit implication including every permitted ordered eigenbasis and f(0)>0.',
}
for a, b in replacements.items():
    assert a in s, a
    s = s.replace(a, b)
a = s.index('# Independently rehash the exact statement and candidate packaging partition.')
b = s.index('config = json.loads', a)
s = s[:a] + '''# Independently rehash exact frozen statements. The complete operational verifier
# binds all candidate inputs and 13 nested manifests against committed Git blobs.
statement = json.loads((P / 'reviews/statement-freeze.json').read_text())
assert len(statement['files']) == 31 and len(statement['source_files']) == 17
for rel, value in statement['files'].items():
    f = P / ({'README.md': 'verification/pre-candidate-README.md'}.get(rel, rel))
    digest = value if isinstance(value, str) else value['sha256']
    assert sha(f) == digest, rel
verified = json.loads(subprocess.check_output([sys.executable, str(E/'verify_inventory.py'), '--live-candidate'], cwd=R))
assert verified['bound_files'] == 703 and verified['nested_manifests'] == 13
assert verified['manifest_sha256'] == case['evidence_sha']
assert sha(P/'verification/final-review-acceptance.json') == 'ed2eef518099d23090e21786b626a111d511b32fea12e7193442273e2d980132'

''' + s[b:]
compile(s, str(out), 'exec')
out.write_text(s)
note = {
    'scope': 'Coordinator-only acceptance-script adaptation; not a proof, evidence or publication change',
    'adapted_from': str(source),
    'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'output_sha256': hashlib.sha256(out.read_bytes()).hexdigest(),
    'initial_preparation_diagnostic': 'An earlier in-memory preparation asserted exactly one recursive final-review-acceptance.json path. It found the live file plus its intentionally retained candidate snapshot and stopped before creating a script or changing any project file. This preparation uses the explicitly observed live verification/final-review-acceptance.json path.',
    'acceptance_execution': 'not yet run',
}
Path('/tmp/nla-lean-formalization/ra09-root-acceptance-adaptation.json').write_text(json.dumps(note, indent=2) + '\n')
print(json.dumps(note, indent=2))
