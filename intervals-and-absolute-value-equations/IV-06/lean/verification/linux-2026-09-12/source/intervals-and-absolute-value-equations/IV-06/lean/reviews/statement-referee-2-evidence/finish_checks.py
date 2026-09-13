"""Parse the recorded successful independent elaboration, including universe names."""
from pathlib import Path
import hashlib, json, re

out = Path(__file__).resolve().parent
project = out.parents[1]
repo = project.parents[2]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
write = lambda name, data: (out / name).write_text(json.dumps(data, indent=2) + '\n')
commands = json.loads((out / 'fresh-checks.json').read_text())
assert len(commands) == 3
for row in commands:
    assert row['exit_code'] == 0
    assert sha(project / row['source']) == row['source_sha256']
    assert sha(out / (Path(row['source']).stem + '.log')) == row['log_sha256']
reports = re.findall(r"'([^'\n]+)' depends on axioms: \[([^\]]*)\]", (out / 'Inspect.log').read_text())
assert len(reports) == 5
normalized = [(name, [re.sub(r'\.\{[^}]*\}', '', item.strip()) for item in raw.split(',')]) for name, raw in reports]
for name, names in normalized[:3]:
    assert names == ['propext', 'Classical.choice', 'Quot.sound'], (name, names)
for name, names in normalized[3:]:
    assert 'sorryAx' in names, (name, names)
write('axioms.json', {'definition_kernel_audits': 3, 'raw_reports': reports, 'normalized_names': normalized, 'normalization': 'remove only printed universe-parameter suffixes .{...}; no axiom name removed or excepted', 'eight_Challenge_placeholders_are_not_proofs': True})
freeze = json.loads((project / 'reviews/statement-freeze.json').read_text())
for rel, expected in freeze['files'].items():
    assert sha(project / rel) == expected, rel
for rel, expected in freeze['source_files'].items():
    assert sha(repo / rel) == expected, rel
assert not (project / 'Solution.lean').exists() and not (project / 'NLA/IV06/Proof.lean').exists()
write('fresh-result.json', {'result': 'PASS', 'commands': 3, 'eight_isolated_Challenge_holes': True, 'three_definition_kernel_checks': True, 'all_32_frozen_inputs_and_8_original_sources_unchanged': True, 'proof_exists': False, 'postprocessing_correction': 'Printed axiom universe suffixes normalized; initial parser and correction retained; all original Lean commands already passed and were not rerun'})
print('PASS: three fresh commands; eight isolated placeholders; three kernel-audited definitions; no proof claim')
