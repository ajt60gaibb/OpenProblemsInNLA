"""Add the explicitly authorized nonmathematical IE23 Comparator selection.

Preserve the original 32+8 frozen inputs and historical handoff. This script
does not implement any proof or claim either independent statement approval.
"""
from pathlib import Path
import datetime, hashlib, json, re, subprocess

PROJECT = Path(__file__).resolve().parents[1]
REPO = PROJECT.parents[2]
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
FREEZE = '6e9b62ab46974a54204ba7636ec83209bd102fd322794709c83a46df85d417f1'
HANDOFF = '14fe26c9ed200eeed620694bc5f1effae62162d03b5bb786ada486875e29e357'
assert sha(PROJECT/'reviews/statement-freeze.json') == FREEZE
assert sha(PROJECT/'reviews/statement-handoff.md') == HANDOFF
f = json.loads((PROJECT/'reviews/statement-freeze.json').read_text())
assert len(f['files']) == 32 and len(f['source_files']) == 8

def integrity():
    for rel, digest in f['files'].items():
        assert sha(PROJECT/rel) == digest, rel
    for rel, digest in f['source_files'].items():
        raw = subprocess.check_output(['git','show',f['base']+':'+rel], cwd=REPO)
        assert hashlib.sha256(raw).hexdigest() == digest, rel
        assert (REPO/rel).read_bytes() == raw, rel
    assert not (PROJECT/'Solution.lean').exists()
    assert not (PROJECT/'NLA/IE23/Proof.lean').exists()

integrity()
names = ['inducedNorm_semantics', 'witness_matrix_identities',
         'fourth_power_norm_control', 'witness_action_identities',
         'witness_attainment', 'witness_norms', 'witness_global_minimizers',
         'not_rightInverseUniqueConjecture']
challenge = (PROJECT/'Challenge.lean').read_text()
assert re.findall(r'^theorem\s+(\w+)\b', challenge, re.M) == names
assert challenge.count('\n  sorry\n') == 8
assert 'namespace NLA.IE23' in challenge
config = {'challenge_module': 'Challenge', 'solution_module': 'Solution',
          'theorem_names': ['NLA.IE23.'+name for name in names],
          'definition_names': [],
          'permitted_axioms': ['propext', 'Classical.choice', 'Quot.sound']}
path = PROJECT/'comparator.json'
assert not path.exists(), 'First-run additive supplement only; do not overwrite a reviewed configuration.'
path.write_text(json.dumps(config, indent=2)+'\n')
assert json.loads(path.read_text()) == config
assert len(config['theorem_names']) == len(set(config['theorem_names'])) == 8
assert 'name = "Solution"' in (PROJECT/'lakefile.toml').read_text()
integrity()
supplement = {
 'phase': 'statement-gate-config-supplement-before-proof',
 'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'author': '/root/leancert_examples',
 'authorization': {
  'sender': '/root',
  'instruction': 'After MI03 referee2 handoff, add only the missing comparator.json with exact eight exports, definition_names=[], and standard-three axioms. Preserve the original 32+8 freeze and historical handoff. Both IE23 referees will approve the union before proof.',
  'mathematical_boundary_change_authorized': False},
 'original_freeze_sha256': FREEZE,
 'original_handoff_sha256': HANDOFF,
 'original_project_inputs_verified_unchanged': f['files'],
 'original_source_inputs_verified_unchanged_against_base_git_blobs': f['source_files'],
 'base': f['base'],
 'added_files': {'comparator.json': {'sha256': sha(path), 'bytes': path.stat().st_size}},
 'supplement_script_sha256': sha(__file__),
 'config_validation': {'status': 'PASS', 'exact_challenge_names': names,
   'all_eight_selected': True, 'duplicate_names': False, 'definition_exceptions': [],
   'permitted_axioms': config['permitted_axioms'], 'modules_registered': True},
 'proof_and_solution_still_absent': True,
 'mathematical_sources_changed': False,
 'new_Lean_elaboration_needed': False,
 'reason': 'Only JSON export selection was added; all elaborated Lean inputs are unchanged. This is not an actual Comparator run.',
 'required_statement_review_boundary': 'Original 32 project inputs plus this comparator.json, and the original eight source inputs. Both independent reviewers must bind this supplement before implementation.',
 'Linux_Comparator_run': False}
record = PROJECT/'reviews/statement-config-supplement.json'
record.write_text(json.dumps(supplement, indent=2)+'\n')
note = PROJECT/'reviews/statement-config-supplement.md'
note.write_text(f'''# IE-23 additive statement-gate configuration supplement

The original statement freeze and historical handoff remain byte-identical.
This parent-authorized supplement adds only `comparator.json`; no Lean
definition, statement, numerical target, source correspondence, dependency pin,
canonical source or status changed. No proof implementation exists.

- Original freeze: `{FREEZE}` (32 project inputs and eight originals).
- Original handoff: `{HANDOFF}`.
- Comparator configuration: `{sha(path)}`.
- Supplement record: `{sha(record)}`.
- Reproduction/validation script: `{sha(__file__)}`.

The configuration selects exactly all eight theorem names in the frozen
Challenge, with Challenge/Solution modules, no definition exceptions, and
only `propext`, `Classical.choice`, `Quot.sound`. Both modules are already
registered; the deliberate Challenge default remains unchanged. All original
inputs were checked before and after the additive write, including original
sources against the actual base Git blobs. JSON validation passed. This is
configuration validation, not a Linux or Comparator execution.

**Proof remains gated.** Both independent statement referees must approve the
union of the original 32+8 inputs and this exact configuration/supplement.
The earlier successful statement elaboration remains applicable because no
Lean or build input changed; no new proof or theorem is claimed here.
''')
print(json.dumps({'status': 'PASS', 'comparator_sha256': sha(path),
 'supplement_json_sha256': sha(record), 'supplement_md_sha256': sha(note),
 'original_32_plus_8_unchanged': True, 'proof_and_solution_absent': True}, indent=2))
