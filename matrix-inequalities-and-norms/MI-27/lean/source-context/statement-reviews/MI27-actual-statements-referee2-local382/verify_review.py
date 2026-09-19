#!/usr/bin/env python3
"""Read-only scope/receipt verification; NEVER a Lean or mathematical checker."""
import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--live', action='store_true', help='also bind exact candidate/evidence paths')
args = parser.parse_args()
checks = 0

def require(condition, message):
    global checks
    if not condition:
        raise AssertionError(message)
    checks += 1

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def lean_text(text):
    out, i, depth = [], 0, 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1
            i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text[i:i+2] == '--':
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    require(depth == 0, 'unclosed Lean comment')
    return ''.join(out)

scope = json.loads((HERE / 'SCOPE.json').read_text())
for rel, h in scope['retained_source'].items():
    require(sha(HERE / rel) == h, f'retained {rel}')
challenge = lean_text((HERE / 'reviewed-source/Challenge.lean').read_text())
defs = lean_text((HERE / 'reviewed-source/Definitions.lean').read_text())
config = json.loads((HERE / 'reviewed-source/comparator.json').read_text())
names = re.findall(r'^theorem\s+(\w+)', challenge, re.M)
require(len(names) == 20 and len(set(names)) == 20, 'twenty unique contracts')
require(config['theorem_names'] == ['NLA.MI27.' + x for x in names], 'exact ordered selection')
require(len(re.findall(r'\bsorry\b', challenge)) == 20, 'twenty intentional placeholders')
require(re.search(r'\b(sorry|axiom|unsafe|native_decide|implemented_by)\b', defs) is None,
        'definitions have no proof escape')
require(re.search(r'\b(axiom|unsafe|native_decide|implemented_by)\b', challenge) is None,
        'reference contracts contain no extra escape')
require(config['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound'],
        'only three standard permitted axioms')
require(config['definition_names'] == [], 'no substitute compared definition')
require(config['challenge_module'] == 'Challenge' and config['solution_module'] == 'Solution',
        'separate reference and implementation modules')
require('CFC.rpow (Xᴴ * X) (1 / 2 : ℝ)' in defs, 'literal full trace norm')
require('def logM' in defs and ':= CFC.log X' in defs, 'actual spectral natural log')
require('ρ.PosDef ∧ Matrix.trace ρ = 1' in defs, 'density hypotheses only')
require('trR (ρ * (logM ρ - logM σ))' in defs, 'ordinary Umegaki expression')
require('‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X‖' in defs, 'Euclidean operator norm')
final = challenge[challenge.index('theorem logarithmic_commutator_bound'):]
require(final.count('(hA : A.PosDef)') == 1 and final.count('(hB : B.PosDef)') == 1,
        'original positive definiteness')
require('(htrace : Matrix.trace (A + B) = 1)' in final, 'original complex trace normalization')
require('traceNorm (B * logM (A + B) - logM (A + B) * B)' in final, 'original commutator')
require('-(trR A) * Real.log (trR A) - (trR B) * Real.log (trR B)' in final,
        'coefficient exactly one')
require('relative_entropy_finite_hockey_stick' not in final and
        'entropy_unitary_mix_derivative' not in final, 'C11/C16 not final premises')

if args.live:
    candidate = Path(scope['candidate'])
    for item in scope['live_bindings']:
        p = Path(item['path'])
        require(sha(p) == item['sha256'], f'live {p}')
    author = json.loads((candidate / 'STATEMENT-AUTHOR-MANIFEST.json').read_text())
    for rel, h in author['files'].items():
        require(sha(candidate / rel) == h, f'author input {rel}')
    require(scope['new_proof_implementation_present_at_review'] is False,
            'recorded statement-only review phase; future proof files are outside scope')
    lock = json.loads((candidate / 'SOURCE-LOCK.json').read_text())
    for item in lock['copies']:
        if item['destination'].startswith('NLA/MI24/'):
            require(sha(Path(item['source'])) == item['sha256'], 'accepted reused source')
            require(sha(candidate / item['destination']) == item['sha256'], 'unchanged retained reuse')
    receipt = json.loads(Path(scope['local_receipt']).read_text())
    require(bool(receipt['end']), 'actual terminal receipt')
    require(receipt['completed_modules'] == 9, 'nine elaborated closure modules')
    require(not receipt['failed_modules'] and not receipt['blocked_modules'], 'no failed/blocked modules')
    commands = receipt['commands']
    require(len(commands) == 9, 'nine commands/reuses')
    require(sum(c.get('status') == 'reused_exact_successful_local_output' for c in commands) == 7,
            'seven authenticated source-matched reuses recorded')
    for command in commands:
        module = command['module']
        rel = module.replace('.', '/') + '.lean'
        require(sha(candidate / rel) == command['source_sha256'], f'receipt source {module}')
        if command.get('status') == 'reused_exact_successful_local_output':
            require(sha(Path(command['prior_receipt'])) == command['prior_receipt_sha256'],
                    'retained prior receipt hash')
            for dep, h in command['transitive_source_hashes'].items():
                require(sha(candidate / dep) == h, f'reused dependency {dep}')
        else:
            require(command['exit_code'] == 0 and command.get('end'), 'fresh successful elaboration')
            require('--threads=1' in command['argv'] and '--memory=4096' in command['argv'],
                    'local resource policy')
            log = Path(scope['local_receipt']).parent / (module + '.log')
            require(sha(log) == command['log_sha256'], 'actual complete log')
            text = log.read_text()
            require('error:' not in text, 'no elaboration error')
            if module == 'Challenge':
                require(text.count('warning: declaration uses `sorry`') == 20,
                        'expected twenty reference warnings')
                require(len(text.splitlines()) == 20, 'no omitted other Challenge log lines')
            else:
                require(text == '', 'empty successful Definitions log')

manifest_path = HERE / 'MANIFEST.json'
if manifest_path.exists():
    manifest = json.loads(manifest_path.read_text())
    for rel, h in manifest['files'].items():
        require(sha(HERE / rel) == h, f'sealed payload {rel}')
    actual = {str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file()
              and p != manifest_path}
    require(actual == set(manifest['files']), 'exact sealed payload set')

print(json.dumps({'status': 'PASS', 'checks': checks, 'live': args.live,
    'scope': 'read-only source/receipt integrity, not Lean/kernel/Comparator or mathematical proof',
    'reviewer_compiler_runs': 0, 'complete_target_count_change': 0}, sort_keys=True))
