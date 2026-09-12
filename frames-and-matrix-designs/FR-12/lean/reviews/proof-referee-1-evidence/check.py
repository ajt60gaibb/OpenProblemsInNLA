"""Independent final referee 1, fresh source elaboration and exact input audit.
Uses this referee's prior campaign approach; does not execute author checkers.
This macOS run reuses pinned dependency artifacts and is not Linux Comparator.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import platform
import re
import subprocess
import tempfile
import time

OUT = Path(__file__).resolve().parent
PROJECT = OUT.parents[1]
REPO = PROJECT.parents[2]
BIN = Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin')
PERMITTED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def save(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2) + '\n')

def capture(argv, cwd=PROJECT):
    return subprocess.check_output(argv, cwd=cwd, text=True).strip()

freeze_path = PROJECT / 'reviews/proof-freeze.json'
assert sha(freeze_path) == 'c65d4deaa3e02af8c20a584dd81b944dbdc72f262e326630e115e5fc9070aa87'
freeze = json.loads(freeze_path.read_text())
assert len(freeze['files']) == 74 and len(freeze['source_files']) == 4
inputs = {}
for key, root in [('files', PROJECT), ('source_files', REPO)]:
    for name, expected in freeze[key].items():
        assert sha(root / name) == expected, name
        inputs[str((root / name).resolve())] = expected
save('inputs-before.json', {'proof_freeze_sha256': sha(freeze_path), 'inputs': inputs})

pins = []
for package in json.loads((PROJECT / 'lake-manifest.json').read_text())['packages']:
    path = PROJECT / '.lake/packages' / package['name']
    current = capture(['git', 'rev-parse', 'HEAD'], path)
    dirty = capture(['git', 'status', '--porcelain'], path)
    assert current == package['rev'] and not dirty, package['name']
    pins.append({'name': package['name'], 'expected': package['rev'],
                 'actual': current, 'git_status_porcelain': dirty})
assert len(pins) == 10
save('dependency-pins.json', pins)

def signatures(source):
    return {name: ' '.join(statement.split()) for name, statement in re.findall(
        r'theorem\s+(\w+)\s+(.*?)\s*:=\s*by', source, flags=re.S)}

challenge = signatures((PROJECT / 'Challenge.lean').read_text())
solution = signatures((PROJECT / 'Solution.lean').read_text())
solution['counting_semantics'] = solution['counting_semantics'].replace('_hn', 'hn')
config = json.loads((PROJECT / 'comparator.json').read_text())
assert len(solution) == 7 and solution == challenge
assert set(solution) == {name.removeprefix('NLA.FR12.') for name in config['theorem_names']}
assert config['definition_names'] == [] and set(config['permitted_axioms']) == PERMITTED
save('signature-check.json', {'result': 'PASS: complete normalized source signatures; sole unused binder alpha-renaming recorded',
                              'not_a_Comparator_result': True, 'signatures': solution, 'config': config})
proof_sources = ['NLA/FR12/Definitions.lean', 'NLA/FR12/Semantics.lean',
                 'NLA/FR12/Doubling.lean', 'NLA/FR12/Growth.lean',
                 'NLA/FR12/Proof.lean', 'Solution.lean']
scan = {}
for name in proof_sources:
    content = (PROJECT / name).read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', content), name
    assert not re.search(r'^import\s+Challenge\b', content, flags=re.M)
    scan[name] = {'sha256': sha(PROJECT / name), 'forbidden_tokens': [], 'imports_Challenge': False}
save('source-scan.json', scan)

prefix_root = Path('/tmp/nla-lean-formalization/independent-prefixes')
prefix_root.mkdir(parents=True, exist_ok=True)
prefix = Path(tempfile.mkdtemp(prefix='fr12-proof-referee1-', dir=prefix_root))
proof_prefix = prefix / 'proof'
challenge_prefix = prefix / 'isolated-challenge'
proof_prefix.mkdir(); challenge_prefix.mkdir()
original_path = capture([str(BIN / 'lake'), 'env', 'printenv', 'LEAN_PATH'])
old_target = (PROJECT / '.lake/build/lib/lean').resolve()
parts = [str(Path(part).resolve()) for part in original_path.split(os.pathsep)
         if Path(part).resolve() != old_target]
assert len(parts) + 1 == len(original_path.split(os.pathsep))
assert all(str(old_target) not in part for part in parts)
env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(proof_prefix), *parts]))
checks = {'independent_referee': '/root/formal_review_standards', 'candidate_author': '/root',
          'date_utc': datetime.now(timezone.utc).isoformat(), 'platform': platform.platform(),
          'lean_version': capture([str(BIN / 'lean'), '--version']),
          'fresh_prefix': str(prefix), 'LEAN_PATH': env['LEAN_PATH'],
          'old_project_build_excluded': str(old_target),
          'scope': 'Fresh source elaboration with pinned compiled dependency reuse; Linux pending',
          'commands': []}
jobs = [(source, source.replace('/', '-').removesuffix('.lean'), 0, proof_prefix)
        for source in proof_sources]
jobs += [('Challenge.lean', 'Challenge', 7, challenge_prefix),
         ('reviews/proof-referee-1-evidence/Inspect.lean', 'Inspect', 0, None)]
for source, label, warnings, output_prefix in jobs:
    cmd = [str(BIN / 'lean')]
    artifacts = []
    if output_prefix is not None:
        for extension, flag in [('.olean', '-o'), ('.ilean', '-i')]:
            target = output_prefix / Path(source).with_suffix(extension)
            target.parent.mkdir(parents=True, exist_ok=True)
            cmd.extend([flag, str(target)]); artifacts.append(target)
    cmd.append(source)
    started = time.monotonic()
    print('Re-elaborating', source, flush=True)
    result = subprocess.run(cmd, cwd=PROJECT, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=300)
    log = OUT / (label + '.log'); log.write_bytes(result.stdout)
    checks['commands'].append({'source': source, 'source_sha256': sha(PROJECT / source),
        'command': cmd, 'exit_code': result.returncode, 'elapsed_seconds': time.monotonic() - started,
        'log': log.name, 'log_sha256': sha(log),
        'artifacts': {str(path.relative_to(prefix)): sha(path) for path in artifacts if path.exists()}})
    save('fresh-checks.json', checks)
    print('Exit', result.returncode, flush=True)
    assert result.returncode == 0, result.stdout.decode()
    assert result.stdout.count(b'warning:') == warnings, result.stdout.decode()
    assert result.stdout.count(b'declaration uses `sorry`') == warnings

axioms = []
for label in ['NLA-FR12-Proof', 'Solution', 'Inspect']:
    for name, value in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", (OUT / (label + '.log')).read_text()):
        names = {item.strip() for item in value.split(',') if item.strip()}
        assert names == PERMITTED, (name, names)
        axioms.append({'declaration': name, 'axioms': sorted(names), 'source_log': label + '.log'})
assert len(axioms) == 21
inspect = (OUT / 'Inspect.log').read_text()
traversed = int(re.search(r'REFEREE_VISITED (\d+)', inspect).group(1))
assert inspect.count('REFEREE_AXIOMS ') == traversed
assert inspect.count('REFEREE_REQUIRED ') == 20
save('axiom-audit.json', {'source_assertions': 14, 'independent_public_assertions': 7,
                        'print_axioms_reports': axioms,
                        'all_reached_project_declarations_audited': traversed,
                        'required_material_dependencies': re.findall(r'REFEREE_REQUIRED ([^\n]+)', inspect)})
for path, expected in inputs.items():
    assert sha(path) == expected, path
assert sha(freeze_path) == 'c65d4deaa3e02af8c20a584dd81b944dbdc72f262e326630e115e5fc9070aa87'
save('inputs-after.json', {'all_74_project_and_4_original_sources_unchanged': True,
                          'proof_freeze_sha256': sha(freeze_path), 'inputs': inputs})
save('result.json', {'result': 'PASS: independent local proof and trust checks',
                    'fresh_commands': 8, 'intentional_Challenge_holes_only': 7,
                    'source_kernel_assertions': 14, 'independent_public_kernel_assertions': 7,
                    'transitively_audited_project_declarations': traversed,
                    'required_material_dependencies': 20, 'clean_pins': 10,
                    'complete_source_signature_matches': 7,
                    'proof_freeze_sha256': sha(freeze_path),
                    'linux_Comparator': 'pending; not run by this local check'})
print('PASS: fresh local proof, full standard-three trust audits, all 78 frozen inputs and ten pins', flush=True)
